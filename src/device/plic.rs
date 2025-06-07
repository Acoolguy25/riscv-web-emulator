#![allow(clippy::unreadable_literal)]
#![allow(unused_imports)]

use crate::cpu::{MIP_MEIP, MIP_SEIP};
use crate::terminal;

// Based on SiFive Interrupt Cookbook
// https://sifive.cdn.prismic.io/sifive/0d163928-2128-42be-a75a-464df65e04e0_sifive-interrupt-cookbook.pdf

/// Emulates PLIC known as Interrupt Controller.
/// Refer to the [specification](https://sifive.cdn.prismic.io/sifive%2Fc89f6e5a-cf9e-44c3-a3db-04420702dcc1_sifive+e31+manual+v19.08.pdf)
/// for the detail.
pub struct Plic {
    irq: u32,
    enabled: u64,
    threshold: u32,
    ips: [u8; 1024],
    priorities: [u32; 1024],
    needs_update_irq: bool,
    virtio_ip_cache: bool,
}

// @TODO: IRQ numbers should be configurable with device tree
const VIRTIO_IRQ: u32 = 1;
const UART_FIRST_IRQ: u32 = 10;
#[allow(dead_code)]
const UART_COUNT: usize = 3;
// const UART_IRQ: u32 = 10;

impl Default for Plic {
    fn default() -> Self {
        Self::new()
    }
}

impl Plic {
    /// Creates a new `Plic`.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            irq: 0,
            enabled: 0,
            threshold: 0,
            priorities: [0; 1024],
            ips: [0; 1024],
            needs_update_irq: false,
            virtio_ip_cache: false,
        }
    }

    /// Runs one cycle. Takes interrupting signals from devices and
    /// raises an interrupt to CPU depending on configuration.
    /// If interrupt occurs a certain bit of `mip` regiser is risen
    /// depending on interrupt type.
    ///
    /// # Arguments
    /// * `virtio_ip`
    /// * `uart_ip`
    /// * `mip`
    /// # Panics
    /// Panics if the conversion of an index `i` to `u32` fails in `u32::try_from(i)`.
    pub fn service(&mut self, virtio_ip: bool, uart_ip: &[bool], mip: &mut u64) {
        // Handling interrupts as "Edge-triggered" interrupt so far

        // Our VirtIO disk implements an interrupt as "Level-triggered" and
        // virtio_ip is always true while interrupt pending bit is asserted.
        // Then our Plic caches virtio_ip and detects the rise edge.
        if self.virtio_ip_cache != virtio_ip {
            if virtio_ip {
                self.set_ip(VIRTIO_IRQ);
            }
            self.virtio_ip_cache = virtio_ip;
        }

        // Our Uart implements an interrupt as "Edge-triggered" and
        // uart_ip is true only at the cycle when an interrupt happens
        for (i, &ip) in uart_ip.iter().enumerate() {
            if ip {
                #[allow(clippy::unwrap_used)]
                self.set_ip(UART_FIRST_IRQ + u32::try_from(i).unwrap()); // or UART_FIRST_IRQ + i
            }
        }
        // else{
            // terminal::log_to_browser!("uart interrupt serviced but not connected!");
        // }

        if self.needs_update_irq {
            self.update_irq(mip);
            self.needs_update_irq = false;
        }
    }

    fn update_irq(&mut self, mip: &mut u64) {
        let mut best_irq   = 0;
        let mut best_prio  = 0;

        // Helper closure: true if this irq line is pending AND enabled
        #[allow(clippy::use_self)]
        let consider = |irq: u32, me: &Plic, best_prio: &mut u32, best_irq: &mut u32| {
            let ip       = ((me.ips[(irq >> 3) as usize] >> (irq & 7)) & 1) == 1;
            let priority = me.priorities[irq as usize];
            let enabled  = ((me.enabled >> irq) & 1) == 1;

            if ip && enabled && priority > me.threshold && priority > *best_prio {
                *best_prio = priority;
                *best_irq  = irq;
            }
        };

        // Check VirtIO
        consider(VIRTIO_IRQ, self, &mut best_prio, &mut best_irq);

        // Check every UART
        for i in 0..UART_COUNT {
            #[allow(clippy::unwrap_used)]
            let irq = UART_FIRST_IRQ + u32::try_from(i).unwrap();
            consider(irq, self, &mut best_prio, &mut best_irq);
        }

        // Latch the result and update MIP
        self.irq = best_irq;
        if self.irq != 0 {
            *mip |= MIP_MEIP | MIP_SEIP;      // raise external interrupt
        } else {
            *mip &= !(MIP_MEIP | MIP_SEIP);   // clear it
        }
    }

    const fn set_ip(&mut self, irq: u32) {
        let index = (irq >> 3) as usize;
        self.ips[index] |= 1 << (irq & 7);
        self.needs_update_irq = true;
    }

    const fn clear_ip(&mut self, irq: u32) {
        let index = (irq >> 3) as usize;
        self.ips[index] &= !(1 << (irq & 7));
        self.needs_update_irq = true;
    }

    /// Loads register content
    ///
    /// # Arguments
    /// * `address`
    #[allow(clippy::cast_possible_truncation)]
    #[must_use]
    pub const fn load(&self, address: u64) -> u8 {
        // terminal::log_to_browser!("PLIC Load AT:{:X}", address);
        match address {
            0x0c000000..=0x0c000fff => {
                let offset = address % 4;
                let index = ((address - 0xc000000) >> 2) as usize;
                let pos = offset << 3;
                (self.priorities[index] >> pos) as u8
            }
            0x0c001000..=0x0c00107f => {
                let index = (address - 0xc001000) as usize;
                self.ips[index]
            }
            0x0c002080 => self.enabled as u8,
            0x0c002081 => (self.enabled >> 8) as u8,
            0x0c002082 => (self.enabled >> 16) as u8,
            0x0c002083 => (self.enabled >> 24) as u8,
            0x0c002084 => (self.enabled >> 32) as u8,
            0x0c002085 => (self.enabled >> 40) as u8,
            0x0c002086 => (self.enabled >> 48) as u8,
            0x0c002087 => (self.enabled >> 56) as u8,
            0x0c201000 => self.threshold as u8,
            0x0c201001 => (self.threshold >> 8) as u8,
            0x0c201002 => (self.threshold >> 16) as u8,
            0x0c201003 => (self.threshold >> 24) as u8,
            0x0c201004 => self.irq as u8,
            0x0c201005 => (self.irq >> 8) as u8,
            0x0c201006 => (self.irq >> 16) as u8,
            0x0c201007 => (self.irq >> 24) as u8,
            _ => 0,
        }
    }

    /// Stores register content
    ///
    /// # Arguments
    /// * `address`
    /// * `value`
    #[allow(clippy::cast_lossless)]
    pub fn store(&mut self, address: u64, value: u8, mip: &mut u64) {
        // terminal::log_to_browser!("PLIC Store AD:{:X} VAL:{:X}", address, value);
        match address {
            0x0c000000..=0x0c000fff => {
                let offset = address % 4;
                let index = ((address - 0xc000000) >> 2) as usize;
                let pos = offset << 3;
                self.priorities[index] =
                    (self.priorities[index] & !(0xff << pos)) | ((value as u32) << pos);
                self.needs_update_irq = true;
            }
            // Enable. Only first 64 interrupt sources support so far.
            // @TODO: Implement all 1024 interrupt source enables.
            0x0c002080 => {
                self.enabled = (self.enabled & !0xff) | (value as u64);
                self.needs_update_irq = true;
            }
            0x0c002081 => {
                self.enabled = (self.enabled & !(0xff << 8)) | ((value as u64) << 8);
            }
            0x0c002082 => {
                self.enabled = (self.enabled & !(0xff << 16)) | ((value as u64) << 16);
            }
            0x0c002083 => {
                self.enabled = (self.enabled & !(0xff << 24)) | ((value as u64) << 24);
            }
            0x0c002084 => {
                self.enabled = (self.enabled & !(0xff << 32)) | ((value as u64) << 32);
            }
            0x0c002085 => {
                self.enabled = (self.enabled & !(0xff << 40)) | ((value as u64) << 40);
            }
            0x0c002086 => {
                self.enabled = (self.enabled & !(0xff << 48)) | ((value as u64) << 48);
            }
            0x0c002087 => {
                self.enabled = (self.enabled & !(0xff << 56)) | ((value as u64) << 56);
            }
            0x0c201000 => {
                self.threshold = (self.threshold & !0xff) | (value as u32);
                self.needs_update_irq = true;
            }
            0x0c201001 => {
                self.threshold = (self.threshold & !(0xff << 8)) | ((value as u32) << 8);
            }
            0x0c201002 => {
                self.threshold = (self.threshold & !(0xff << 16)) | ((value as u32) << 16);
            }
            0x0c201003 => {
                self.threshold = (self.threshold & !(0xff << 24)) | ((value as u32) << 24);
            }
            // Claim
            0x0c201004 => {
                // Assuming written data is a byte so far
                // @TODO: Should be four bytes.
                self.clear_ip(value as u32);
            }
            _ => {}
        }
        if self.needs_update_irq {
            self.update_irq(mip);
            self.needs_update_irq = false;
        }
    }
}
