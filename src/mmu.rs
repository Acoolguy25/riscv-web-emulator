#![allow(clippy::unreadable_literal, clippy::cast_possible_wrap)]

use crate::cpu;
use crate::csr;
use crate::device::clint::Clint;
use crate::device::plic::Plic;
use crate::device::uart::Uart;
use crate::device::rtc::RTC;
use crate::device::virtio_block_disk::VirtioBlockDisk;
use crate::device::sys::Sys;
pub use crate::memory::*;
use crate::riscv;
use crate::terminal::Terminal;
use crate::terminal;
use cpu::{
    CONFIG_SW_MANAGED_A_AND_D, Exception, MSTATUS_MPP_SHIFT, MSTATUS_MPRV, MSTATUS_MXR,
    MSTATUS_SUM, PG_SHIFT,
};
use csr::SATP_MODE_MASK;
use csr::SATP_MODE_SHIFT;
use csr::SATP_PPN_MASK;
use csr::SATP_PPN_SHIFT;
use csr::SatpMode;
use fnv::FnvHashMap;
use log::trace;
use log::warn;
use riscv::MemoryAccessType;
use riscv::PrivMode;
use riscv::Trap;
use riscv::priv_mode_from;

// use std::mem;

const DTB_SIZE: usize = 0xfe0;

/// Emulates Memory Management Unit. It holds the Main memory and peripheral
/// devices, maps address to them, and accesses them depending on address.
///
/// It also manages virtual-physical address translation and memory protection.
/// It could also be called Bus.
pub struct Mmu {
    // CPU state that lives here
    pub prv: PrivMode,
    pub mstatus: u64,
    pub mip: u64,
    pub satp: u64,

    pub memory: Memory,
    dtb: Vec<u8>,
    disk: VirtioBlockDisk,
    plic: Plic,
    clint: Clint,
    uart: Vec<Uart>,
    rtc: RTC,
    sys: Sys,

    /// Address translation page cache.
    /// The cache is cleared when translation mapping can be changed;
    /// SATP, or PRV is updated or FENCE.VMA is executed.
    /// Technically page table entries
    /// can be updated anytime with store instructions, but RISC-V
    /// allows for this and requires that FENCE.VMA is executed before
    /// any of these are observed.
    /// If you want to enable, use `enable_page_cache()`.
    page_cache_enabled: bool,
    fetch_page_cache: FnvHashMap<u64, u64>,
    load_page_cache: FnvHashMap<u64, u64>,
    store_page_cache: FnvHashMap<u64, u64>,
}


pub const PTE_V_MASK: u64 = 1 << 0;
pub const PTE_U_MASK: u64 = 1 << 4;
pub const PTE_A_MASK: u64 = 1 << 6;
pub const PTE_D_MASK: u64 = 1 << 7;

impl Mmu {
    /// Creates a new `Mmu`.
    ///
    /// # Arguments
    /// * `xlen`
    /// * `terminal`
    #[must_use]
    pub fn new(terminals: Vec<Box<dyn Terminal>>) -> Self {
        let mut dtb = vec![0; DTB_SIZE];

        // Load default device tree binary content
        let content = include_bytes!("./device/dtb.dtb");
        dtb[..content.len()].copy_from_slice(&content[..]);

        let mut uart_list: Vec<Uart> = Vec::new();
        for (idx, terminal) in terminals.into_iter().enumerate() {
            uart_list.push(Uart::new(terminal, idx as u8));
        }

        Self {
            prv: PrivMode::M,
            mstatus: 0,
            mip: 0,
            satp: 0,
            memory: Memory::new(),
            dtb,
            disk: VirtioBlockDisk::new(),
            plic: Plic::new(),
            clint: Clint::new(),
            uart: uart_list,
            rtc: RTC::new(),
            sys: Sys::new(),
            page_cache_enabled: false,
            fetch_page_cache: FnvHashMap::default(),
            load_page_cache: FnvHashMap::default(),
            store_page_cache: FnvHashMap::default(),
        }
    }

    /// Initializes Main memory. This method is expected to be called only once.
    ///
    /// # Arguments
    /// * `capacity`
    pub fn init_memory(&mut self, capacity: usize) {
        self.memory.init(capacity);
    }

    /// Initializes Virtio block disk. This method is expected to be called only once.
    ///
    /// # Arguments
    /// * `data` Filesystem binary content
    pub fn init_disk(&mut self, data: Vec<u8>) {
        self.disk.init(data);
    }

    /// Overrides default Device tree configuration.
    ///
    /// # Arguments
    /// * `data` DTB binary content
    pub fn init_dtb(&mut self, data: &[u8]) {
        self.dtb[..data.len()].copy_from_slice(data);
        for i in data.len()..self.dtb.len() {
            self.dtb[i] = 0;
        }
    }

    /// Enables or disables page cache optimization.
    ///
    /// # Arguments
    /// * `enabled`
    pub fn enable_page_cache(&mut self, enabled: bool) {
        self.page_cache_enabled = enabled;
        self.clear_page_cache();
    }

    /// Clears page cache entries
    pub fn clear_page_cache(&mut self) {
        self.fetch_page_cache.clear();
        self.load_page_cache.clear();
        self.store_page_cache.clear();
    }

    pub fn service(&mut self, cycle: u64) {
        // --- timers & disk ---------------------------------------------------
        self.clint.service(cycle, &mut self.mip);
        self.disk.service(&mut self.memory, cycle);

        // --- UARTs -----------------------------------------------------------
        // Collect one interrupt-pending flag per UART
        let mut uart_ip: Vec<bool> = Vec::with_capacity(self.uart.len());
        for uart in &mut self.uart {
            uart.service();                    // run the UART
            uart_ip.push(uart.is_interrupting());
        }

        // --- send all device IRQs to the PLIC -------------------------------
        self.plic.service(
            self.disk.is_interrupting(),  // VirtIO-disk level IRQ
            &uart_ip,                     // slice of UART IRQs
            &mut self.mip,                // write-back to MIP
        );
    }


    /// Updates privilege mode
    ///
    /// # Arguments
    /// * `mode`
    pub fn update_priv_mode(&mut self, mode: PrivMode) {
        self.prv = mode;
        self.clear_page_cache();
    }

    /// Loads an byte. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// # Errors
    /// Exceptions are returned as errors
    pub fn load_virt_u8(&mut self, va: u64) -> Result<u8, Exception> {
        let pa = self.translate_address(va, MemoryAccessType::Read, false)?;
        Ok(self.load_phys_u8(pa))
    }

    /// Loads multiple bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `width` Must be 1, 2, 4, or 8
    fn load_virt_bytes(&mut self, va: u64, width: u64) -> Result<u64, Exception> {
        debug_assert!(
            width == 1 || width == 2 || width == 4 || width == 8,   
            "Width must be 1, 2, 4, or 8. {width:X}"
        );
        if va & 0xfff <= 0x1000 - width {
            // Fast path. All bytes fetched are in the same page so
            // translating an address only once.
            let pa = self.translate_address(va, MemoryAccessType::Read, false)?;
            Ok(match width {
                1 => u64::from(self.load_phys_u8(pa)),
                2 => u64::from(self.load_phys_u16(pa)),
                4 => u64::from(self.load_phys_u32(pa)),
                8 => self.load_phys_u64(pa),
                _ => panic!("Width must be 1, 2, 4, or 8. {width:X}"),
            })
        } else {
            let mut data = 0_u64;
            for i in 0..width {
                let byte = self.load_virt_u8(va.wrapping_add(i))?;
                data |= u64::from(byte) << (i * 8);
            }
            Ok(data)
        }
    }

    /// Loads four bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// # Errors
    /// Exceptions are returned as errors
    //
    // XXX Still being used by the atomics
    #[allow(clippy::cast_possible_truncation)]
    pub fn load_virt_u32(&mut self, va: u64) -> Result<u32, Exception> {
        match self.load_virt_bytes(va, 4) {
            Ok(data) => Ok(data as u32),
            Err(e) => Err(e),
        }
    }

    /// Loads eight bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// # Errors
    /// Exceptions are returned as errors
    pub fn load_virt_u64(&mut self, va: u64) -> Result<u64, Exception> {
        match self.load_virt_bytes(va, 8) {
            Ok(data) => Ok(data),
            Err(e) => Err(e),
        }
    }

    /// Loads eight bytes as i64. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// # Errors
    /// Exceptions are returned as errors
    // XXX in contrast to `load_virt_u64` it takes the address as i64.  Eventually all the memory
    // ops will do this, but for the moment we have this odd ugliness
    #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
    pub fn load_virt_u64_(&mut self, va: i64) -> Result<i64, Exception> {
        // XXX All addresses should be i64
        Ok(self.load_virt_bytes(va as u64, 8)? as i64)
    }

    /// Store an byte. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `value`
    /// # Errors
    /// Exceptions are returned as errors
    pub fn store_virt_u8(&mut self, va: u64, value: u8) -> Result<(), Exception> {
        let pa = self.translate_address(va, MemoryAccessType::Write, false)?;
        self.store_phys_u8(pa, value).map_err(|()| Exception {
            trap: Trap::StoreAccessFault,
            tval: va as i64,
        })
    }

    /// Stores multiple bytes. This method takes a virtual address and translates
    /// it into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `value` data written
    /// * `width` Must be 1, 2, 4, or 8
    /// # Errors
    /// Exceptions are returned as errors
    /// # Panics
    /// width must be 1, 2, 4, or 8
    #[allow(clippy::cast_possible_truncation)]
    pub fn store_virt_bytes(&mut self, va: u64, value: u64, width: u64) -> Result<(), Exception> {
        debug_assert!(
            width == 1 || width == 2 || width == 4 || width == 8,
            "Width must be 1, 2, 4, or 8. {width:X}"
        );
        if va & 0xfff <= 0x1000 - width {
            // Fast path. All bytes fetched are in the same page so
            // translating an address only once.
            let pa = self.translate_address(va, MemoryAccessType::Write, false)?;
            let r = match width {
                1 => self.store_phys_u8(pa, value as u8),
                2 => self.store_phys_u16(pa, value as u16),
                4 => self.store_phys_u32(pa, value as u32),
                8 => self.store_phys_u64(pa, value),
                _ => panic!("Width must be 1, 2, 4, or 8. {width:X}"),
            };
            r.map_err(|()| Exception {
                trap: Trap::StoreAccessFault,
                tval: va as i64,
            })
        } else {
            for i in 0..width {
                self.store_virt_u8(va.wrapping_add(i), ((value >> (i * 8)) & 0xff) as u8)?;
            }
            Ok(())
        }
    }

    /// Stores two bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `value` data written
    /// # Errors
    /// Exceptions are returned as errors
    pub fn store_virt_u16(&mut self, va: u64, value: u16) -> Result<(), Exception> {
        self.store_virt_bytes(va, u64::from(value), 2)
    }

    /// Stores four bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `value` data written
    /// # Errors
    /// Exceptions are returned as errors
    pub fn store_virt_u32(&mut self, va: u64, value: u32) -> Result<(), Exception> {
        self.store_virt_bytes(va, u64::from(value), 4)
    }

    /// Stores eight bytes. This method takes virtual address and translates
    /// into physical address inside.
    ///
    /// # Arguments
    /// * `va` Virtual address
    /// * `value` data written
    /// # Errors
    /// Exceptions are returned as errors
    pub fn store_virt_u64(&mut self, va: u64, value: u64) -> Result<(), Exception> {
        self.store_virt_bytes(va, value, 8)
    }

    /// # Errors
    /// Exceptions are returned as errors
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub fn store64(&mut self, va: i64, value: i64) -> Result<(), Exception> {
        self.store_virt_bytes(va as u64, value as u64, 8)
    }

    /// # Errors
    /// Exceptions are returned as errors
    // XXX in contrast to `store_virt_u32` it takes the address and data as i64.
    // Eventually all the memory ops will do this, but for the moment we have this odd ugliness
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub fn store_virt_u32_(&mut self, va: i64, value: i64) -> Result<(), Exception> {
        self.store_virt_bytes(va as u64, value as u64, 4)
    }

    /// Loads a byte from main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    /// # Panics
    /// Can panic ...
    #[allow(clippy::cast_possible_truncation, clippy::unwrap_used)]
    pub fn load_phys_u8(&mut self, pa: u64) -> u8 {
        // @TODO: Mapping should be configurable with dtb
        if pa >= DRAM_BASE {
            self.memory.read_u8(pa)
        } else {
            self.load_mmio_u8(pa).unwrap()
        }
    }

    /// # Errors
    /// Cannot really panic
    #[allow(clippy::result_unit_err, clippy::cast_possible_truncation)]
    pub fn load_mmio_u8(&mut self, pa: u64) -> Result<u8, ()> {
        match pa {
            // I don't know why but dtb data seems to be stored from 0x1020 on Linux.
            // It might be from self.x[0xb] initialization?
            // And DTB size is arbitray.
            0x00001020..=0x00001fff => Ok(self.dtb[pa as usize - 0x1020]),
            0x02000000..=0x0200ffff => Ok(self.clint.load(pa)),
            0x0C000000..=0x0fffffff => Ok(self.plic.load(pa)),
            0x10000000..=0x100000ff => Ok(self.uart[0].load(pa)),
            0x10000100..=0x100001ff => Ok(self.sys.load(pa)), // sys
            0x10000200..=0x100002ff => Ok(self.uart[1].load(pa)), // uart 2
            0x10000400..=0x100004ff => Ok(self.uart[2].load(pa)), // uart 3
            0x10001000..=0x10001FFF => Ok(self.disk.load(pa)),
            0x10002000..=0x10002007 => Ok(self.rtc.load(pa)), // rtc
            
            _ => {
                terminal::log_to_browser!("Load failed at {}", pa);
                Ok(0)
            },
        }
    }

    /// Loads two bytes from main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    fn load_phys_u16(&mut self, pa: u64) -> u16 {
        if pa >= DRAM_BASE && pa.wrapping_add(1) > pa {
            // Fast path. Directly load main memory at a time.
            self.memory.read_u16(pa)
        } else {
            let mut data = 0_u16;
            for i in 0..2 {
                data |= u16::from(self.load_phys_u8(pa.wrapping_add(i))) << (i * 8);
            }
            data
        }
    }

    /// Loads four bytes from main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    pub fn load_phys_u32(&mut self, pa: u64) -> u32 {
        if pa >= DRAM_BASE && pa.wrapping_add(3) > pa {
            self.memory.read_u32(pa)
        } else {
            let mut data = 0_u32;
            for i in 0..4 {
                data |= u32::from(self.load_phys_u8(pa.wrapping_add(i))) << (i * 8);
            }
            data
        }
    }

    /// Loads eight bytes from main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    pub fn load_phys_u64(&mut self, pa: u64) -> u64 {
        if pa >= DRAM_BASE && pa.wrapping_add(7) > pa {
            self.memory.read_u64(pa)
        } else {
            let mut data = 0_u64;
            for i in 0..8 {
                data |= u64::from(self.load_phys_u8(pa.wrapping_add(i))) << (i * 8);
            }
            data
        }
    }

    /// Stores a byte to main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    /// * `value` data written
    /// # Errors
    /// Will return error for access outside supported memory range
    #[allow(clippy::result_unit_err, clippy::cast_sign_loss)]
    pub fn store_mmio_u8(&mut self, pa: i64, value: u8) -> Result<(), ()> {
        // terminal::log_to_browser!("mmu store 0x{:X} at 0x{:X}, uart: {}", pa, value, self.uart.len());
        let pa = pa as u64;
        match pa {
            0x02000000..=0x0200ffff => self.clint.store(pa, value, &mut self.mip),
            0x0c000000..=0x0fffffff => self.plic.store(pa, value, &mut self.mip),
            0x10000000..=0x100000ff => self.uart[0].store(pa, value),
            0x10000100..=0x100001ff => self.sys.store(pa, value), // sys
            0x10000200..=0x100002ff => self.uart[1].store(pa, value), // uart 2

            0x10000400..=0x100004ff => self.uart[2].store(pa, value), // uart 3
            0x10001000..=0x10001FFF => self.disk.store(pa, value),
            0x10002000..=0x10002007 => self.rtc.store(pa, value), // rtc
            _ => {
                terminal::log_to_browser!("Store failed at {}", pa);
                return Err(())
            },
        }
        Ok(())
    }

    /// # Panics
    /// It can panic which is bad and which is why it's going away soon
    /// # Errors
    /// If any part of the access is outside of memory, a unit error is returned
    #[allow(
        clippy::unwrap_used,
        clippy::result_unit_err,
        clippy::cast_possible_wrap
    )]
    pub fn store_phys_u8(&mut self, pa: u64, value: u8) -> Result<(), ()> {
        // @TODO: Mapping should be configurable with dtb
        if DRAM_BASE <= pa {
            self.memory.write_u8(pa, value)
        } else {
            self.store_mmio_u8(pa as i64, value)
        }
    }

    /// Stores two bytes to main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    /// * `value` data written
    /// # Panics
    /// It can panic which is bad and which is why it's going away soon
    /// # Errors
    /// If any part of the access is outside of memory, a unit error is returned
    #[allow(clippy::result_unit_err)]
    pub fn store_phys_u16(&mut self, pa: u64, value: u16) -> Result<(), ()> {
        if pa >= DRAM_BASE {
            self.memory.write_u16(pa, value)
        } else {
            for i in 0..2 {
                self.store_phys_u8(pa.wrapping_add(i), ((value >> (i * 8)) & 0xff) as u8)?;
            }
            Ok(())
        }
    }

    /// Stores four bytes to main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    /// * `value` data written
    /// # Errors
    /// If any part of the access is outside of memory, a unit error is returned
    #[allow(clippy::result_unit_err)]
    pub fn store_phys_u32(&mut self, pa: u64, value: u32) -> Result<(), ()> {
        if pa >= DRAM_BASE {
            self.memory.write_u32(pa, value)
        } else {
            for i in 0..4 {
                self.store_phys_u8(pa.wrapping_add(i), ((value >> (i * 8)) & 0xff) as u8)?;
            }
            Ok(())
        }
    }

    /// Stores eight bytes to main memory or peripheral devices depending on
    /// physical address.
    ///
    /// # Arguments
    /// * `pa` Physical address
    /// * `value` data written
    /// # Errors
    /// If any part of the access is outside of memory, a unit error is returned
    #[allow(clippy::result_unit_err)]
    pub fn store_phys_u64(&mut self, pa: u64, value: u64) -> Result<(), ()> {
        if pa >= DRAM_BASE {
            self.memory.write_u64(pa, value)
        } else {
            for i in 0..8 {
                self.store_phys_u8(pa.wrapping_add(i), ((value >> (i * 8)) & 0xff) as u8)?;
            }
            Ok(())
        }
    }

    /// # Errors
    /// If this fails then the error will have the exception that should be raised
    pub fn translate_address(
        &mut self,
        address: u64,
        access_type: MemoryAccessType,
        side_effect_free: bool,
    ) -> Result<u64, Exception> {
        let v_page = address & !0xfff;

        let cache = if self.page_cache_enabled {
            match access_type {
                MemoryAccessType::Execute => self.fetch_page_cache.get(&v_page),
                MemoryAccessType::Read => self.load_page_cache.get(&v_page),
                MemoryAccessType::Write => self.store_page_cache.get(&v_page),
            }
        } else {
            None
        };

        if let Some(p_page) = cache {
            return Ok(p_page | (address & 0xfff));
        }

        let pa = self.translate_address_slow(address, access_type, side_effect_free)?;

        if self.page_cache_enabled && !side_effect_free {
            let p_page = pa & !0xfff;
            let _ = match access_type {
                MemoryAccessType::Execute => self.fetch_page_cache.insert(v_page, p_page),
                MemoryAccessType::Read => self.load_page_cache.insert(v_page, p_page),
                MemoryAccessType::Write => self.store_page_cache.insert(v_page, p_page),
            };
        }

        Ok(pa)
    }

    #[allow(
        clippy::cast_possible_wrap,
        clippy::too_many_lines,
        clippy::expect_used,
        clippy::cognitive_complexity
    )]
    fn translate_address_slow(
        &mut self,
        va: u64,
        access: MemoryAccessType,
        side_effect_free: bool,
    ) -> Result<u64, Exception> {
        let prv = self.prv;
        let effective_prv =
            if self.mstatus & MSTATUS_MPRV != 0 && access != MemoryAccessType::Execute {
                // Use previous privilege
                priv_mode_from((self.mstatus >> MSTATUS_MPP_SHIFT) & 3)
            } else {
                prv
            };

        let satp_mode = ((self.satp >> SATP_MODE_SHIFT) & SATP_MODE_MASK) as usize;
        if effective_prv == PrivMode::M || satp_mode == SatpMode::Bare as usize {
            return Ok(va);
        }

        // Sv39, Sv48, Sv57
        let levels = 3 + satp_mode - SatpMode::Sv39 as usize;
        let access_shift = match access {
            MemoryAccessType::Read => 0,
            MemoryAccessType::Write => 1,
            MemoryAccessType::Execute => 2,
        };

        let pte_size_log2 = 3;
        let vaddr_shift = 64 - (PG_SHIFT + levels * 9);
        // Check for canonical addresses
        if ((va as i64) << vaddr_shift) >> vaddr_shift != va as i64 {
            // XXX Some debugging logging here might be useful
            return page_fault(va as i64, access);
        }
        let pte_addr_bits = 44;
        let page_table_root = (self.satp >> SATP_PPN_SHIFT) & SATP_PPN_MASK;
        let mut pte_addr = (page_table_root & ((1 << pte_addr_bits) - 1)) << PG_SHIFT;
        let pte_bits = 12 - pte_size_log2;
        let pte_mask = (1 << pte_bits) - 1;

        for i in 0..levels {
            let vaddr_shift = PG_SHIFT + pte_bits * (levels - 1 - i);
            let pte_idx = (va >> vaddr_shift) & pte_mask;
            pte_addr += pte_idx << pte_size_log2;
            // XXX Not only do we need to raise an exception if this
            // fails, but failing here doesn't cause a page fault but
            // just a fault (eg CAUSE_FAULT_LOAD/STORE instead of all
            // the others which are
            // CAUSE_LOAD/STORE/FETCH_PAGE_FAULT).
            let pte = self.load_phys_u64(pte_addr);
            // return access_fault(address, access_type);

            if pte & PTE_V_MASK == 0 {
                trace!("** {prv:?} mode access to {va:08x} denied: invalid PTE");
                break;
            }

            // XXX too many hardcoded values
            let paddr = (pte >> 10) << PG_SHIFT;
            let mut xwr = (pte >> 1) & 7;
            if xwr == 0 {
                pte_addr = paddr;
                continue;
            }

            // *** Found a leaf node ***

            if xwr == 2 || xwr == 6 {
                trace!("** {prv:?} mode access to {va:08x} denied: invalid xwr {xwr}");
                break;
            }

            // priviledge check
            if effective_prv == PrivMode::S {
                if pte & PTE_U_MASK != 0 && self.mstatus & MSTATUS_SUM == 0 {
                    // XXX Debug log would be useful
                    warn!("** {prv:?} mode access to {va:08x} denied: U & !SUM");
                    break;
                }
            } else if pte & PTE_U_MASK == 0 {
                // XXX Debug log would be useful
                warn!("** {prv:?} mode access to {va:08x} denied: !U");
                return page_fault(va as i64, access);
            }

            /* protection check */
            /* MXR allows read access to execute-only pages */
            if self.mstatus & MSTATUS_MXR != 0 {
                xwr |= xwr >> 2;
            }

            if (xwr >> access_shift) & 1 == 0 {
                let want = 1 << access_shift;
                trace!("** {prv:?} mode access to {va:08x} denied: want {want}, got {xwr}");
                break;
            }

            /* 6. Check for misaligned superpages */
            let ppn = pte >> 10;
            let j = levels - 1 - i;
            if ((1 << j) - 1) & ppn != 0 {
                warn!("** access to {va:08x} denied: misaligned superpage {i} / {ppn}");
                break;
            }

            /*
              RISC-V Priv. Spec 1.11 (draft) Section 4.3.1 offers two
              ways to handle the A and D TLB flags.  Spike uses the
              software managed approach whereas Dromajo used to manage
              them (causing far fewer exceptions).
            */
            if CONFIG_SW_MANAGED_A_AND_D {
                if pte & PTE_A_MASK == 0 {
                    trace!("** {prv:?} mode access to {va:08x} denied: missing A");
                    break; // Must have A on access
                }
                if access == MemoryAccessType::Write && pte & PTE_D_MASK == 0 {
                    trace!("** {prv:?} mode access to {va:08x} denied: missing D");
                    break; // Must have D on write
                }
            } else {
                let mut new_pte = pte | PTE_A_MASK;
                if access == MemoryAccessType::Write {
                    new_pte |= PTE_D_MASK;
                }
                if pte != new_pte
                    && !side_effect_free
                    && self.store_phys_u64(pte_addr, new_pte).is_err()
                {
                    return access_fault(va as i64, access);
                }
            }

            let vaddr_mask = (1 << vaddr_shift) - 1;
            return Ok(paddr & !vaddr_mask | va & vaddr_mask);
        }

        page_fault(va as i64, access)
    }

    /// Returns immutable reference to `Clint`.
    #[must_use]
    pub const fn get_clint(&self) -> &Clint {
        &self.clint
    }

    /// Returns mutable reference to `Clint`.
    pub const fn get_mut_clint(&mut self) -> &mut Clint {
        &mut self.clint
    }

    /// Returns mutable reference to `Uart`.
    pub fn get_mut_uart(&mut self, idx: u8) -> &mut Uart {
        &mut self.uart[idx as usize]
    }
}

#[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)] // XXX Try to remove this later when the u64 -> i64 conversion is done
const fn page_fault<T>(address: i64, access_type: MemoryAccessType) -> Result<T, Exception> {
    Err::<T, Exception>(Exception {
        trap: match access_type {
            MemoryAccessType::Read => Trap::LoadPageFault,
            MemoryAccessType::Write => Trap::StorePageFault,
            MemoryAccessType::Execute => Trap::InstructionPageFault,
        },
        tval: address,
    })
}

#[allow(clippy::cast_sign_loss, clippy::cast_possible_wrap)] // XXX Try to remove this later when the u64 -> i64 conversion is done
const fn access_fault<T>(address: i64, access_type: MemoryAccessType) -> Result<T, Exception> {
    Err::<T, Exception>(Exception {
        trap: match access_type {
            MemoryAccessType::Read => Trap::LoadAccessFault,
            MemoryAccessType::Write => Trap::StoreAccessFault,
            MemoryAccessType::Execute => Trap::InstructionAccessFault,
        },
        tval: address,
    })
}
