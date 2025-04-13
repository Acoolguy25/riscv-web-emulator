#![allow(clippy::unreadable_literal)]

// @TODO: temporal
const TEST_MEMORY_CAPACITY: usize = 1024 * 1024 * 256;
const PROGRAM_MEMORY_CAPACITY: usize = 1024 * 1024 * 512; // big enough to run Linux and xv6

pub mod cpu;
pub mod csr;
mod dag_decoder;
pub mod default_terminal;
pub mod device;
pub mod elf_analyzer;
pub mod fp;
pub mod memory;
pub mod mmu;
pub mod riscv;
pub mod rvc;
pub mod terminal;

use crate::cpu::Cpu;
use crate::elf_analyzer::ElfAnalyzer;
use crate::terminal::Terminal;
use fnv::FnvHashMap;

/// RISC-V emulator. It emulates RISC-V CPU and peripheral devices.
///
/// Sample code to run the emulator.
/// ```ignore
/// // Creates an emulator with arbitary terminal
/// let mut emulator = Emulator::new(Box::new(DefaultTerminal::new()));
/// // Set up program content binary
/// emulator.setup_program(program_content);
/// // Set up Filesystem content binary
/// emulator.setup_filesystem(fs_content);
/// // Go!
/// emulator.run();
/// ```
pub struct Emulator {
    cpu: Cpu,

    /// Stores mapping from symbol to virtual address
    symbol_map: FnvHashMap<String, u64>,

    /// [`riscv-tests`](https://github.com/riscv/riscv-tests) program specific
    /// properties. Whether the program set by `setup_program()` is
    /// [`riscv-tests`](https://github.com/riscv/riscv-tests) program.
    is_test: bool,

    /// [`riscv-tests`](https://github.com/riscv/riscv-tests) specific properties.
    /// The address where data will be sent to terminal
    tohost_addr: u64,
}

impl Emulator {
    /// Creates a new `Emulator`. [`Terminal`](terminal/trait.Terminal.html)
    /// is internally used for transferring input/output data to/from `Emulator`.
    ///
    /// # Arguments
    /// * `terminal`
    #[must_use]
    pub fn new(terminal: Box<dyn Terminal>) -> Self {
        Self {
            cpu: Cpu::new(terminal),

            symbol_map: FnvHashMap::default(),

            // These can be updated in setup_program()
            is_test: false,
            tohost_addr: 0, // assuming tohost_addr is non-zero if exists
        }
    }

    /// Runs program set by `setup_program()`. Calls `run_test()` if the program
    /// is [`riscv-tests`](https://github.com/riscv/riscv-tests).
    /// Otherwise calls `run_program()`.
    pub fn run(&mut self, trace: bool) {
        if trace {
            self.run_test();
        } else {
            self.run_program();
        }
    }

    /// Runs program set by `setup_program()`. The emulator will run forever.
    pub fn run_program(&mut self) {
        loop {
            self.tick(40);
            if self.handle_htif() {
                break;
            }
        }
    }

    /// Method for running [`riscv-tests`](https://github.com/riscv/riscv-tests) program.
    /// The differences from `run_program()` are
    /// * Disassembles every instruction and dumps to terminal
    /// * The emulator stops when the test finishes
    /// * Displays the result message (pass/fail) to terminal
    /// # Panics
    /// It can panic
    #[allow(clippy::cast_possible_truncation)]
    pub fn run_test(&mut self) {
        //use std::io::{self, Write};

        let mut s = String::new();
        loop {
            s.clear();
            let wbr = self.cpu.disassemble(&mut s);
            self.tick(1);
            let cycle = self.cpu.cycle;
            print!("{cycle:5} {s:72}");
            if wbr != 0 {
                println!("{:16x}", self.cpu.read_register(wbr as u8));
            } else {
                println!();
            }
            //let _ = io::stdout().flush();

            if self.handle_htif() {
                break;
            }
        }
    }

    fn handle_htif(&mut self) -> bool {
        // The insanity: https://github.com/riscv-software-src/riscv-isa-sim/issues/364#issuecomment-607657754
        if self.tohost_addr == 0 {
            return false;
        }
        let tohost = self.cpu.get_mut_mmu().load_phys_u64(self.tohost_addr);
        if tohost == 0 {
            return false;
        }

        let device = tohost >> 56;
        let command = (tohost >> 48) & 0xff;
        let payload = tohost & 0xFFFF_FFFF_FFFF;
        if payload % 2 == 1 {
            // Riscv-tests terminates by writing the result * 2 + 1 to `tohost`
            // Zero means pass, anything else encodes where it failed.
            match payload / 2 {
                0 => println!("Test Passed"),
                exit_code => println!("Test Failed with {exit_code}"),
            }
            return true;
        }

        if device == 0 {
            // System call
            //  magic_mem[0] = which;
            //  magic_mem[1] = arg0;
            //  magic_mem[2] = arg1;
            //  magic_mem[3] = arg2;
            let which = self.cpu.get_mut_mmu().load_phys_u64(payload);
            let arg0 = self.cpu.get_mut_mmu().load_phys_u64(payload + 8);
            let arg1 = self.cpu.get_mut_mmu().load_phys_u64(payload + 16);
            let arg2 = self.cpu.get_mut_mmu().load_phys_u64(payload + 24);
            match which {
                0x40 => {
                    // write
                    assert_eq!(arg0, 1);
                    for i in 0..arg2 {
                        print!("{}", self.cpu.get_mut_mmu().load_phys_u8(arg1 + i) as char);
                    }
                }
                syscall => todo!("System call {syscall}"),
            }
        } else if device == 1 {
            assert_eq!(command, 1); // Command 0 is read a char, not supported
            print!("{}", command as u8 as char);
        }

        // Ack
        let _ = self.cpu.get_mut_mmu().store_phys_u64(self.tohost_addr, 0);
        let _ = self
            .cpu
            .get_mut_mmu()
            .store_phys_u64(self.tohost_addr + 64, 1); // from_host
        false
    }

    /// Runs CPU one cycle
    pub fn tick(&mut self, n: usize) {
        // XXX We should be able to set this arbitrarily high, but we seem
        // to hit a race condition and a Linux hang beyond this value
        self.cpu.run_soc(n);
    }

    /// Sets up program run by the program. This method analyzes the passed content
    /// and configure CPU properly. If the passed contend doesn't seem ELF file,
    /// it panics. This method is expected to be called only once.
    ///
    /// # Arguments
    /// * `data` Program binary
    /// # Panics
    /// Will panic if given a non-Elf file
    // @TODO: Make ElfAnalyzer and move the core logic there.
    // @TODO: Returns `Err` if the passed contend doesn't seem ELF file
    #[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
    pub fn setup_program(&mut self, data: Vec<u8>) {
        let analyzer = ElfAnalyzer::new(data);

        assert!(analyzer.validate(), "This file does not seem ELF file");

        let header = analyzer.read_header();
        //let program_headers = analyzer._read_program_headers(&header);
        let section_headers = analyzer.read_section_headers(&header);

        let mut program_data_section_headers = vec![];
        let mut symbol_table_section_headers = vec![];
        let mut string_table_section_headers = vec![];

        for sh in &section_headers {
            match sh.sh_type {
                1 => program_data_section_headers.push(sh),
                2 => symbol_table_section_headers.push(sh),
                3 => string_table_section_headers.push(sh),
                _ => {}
            }
        }

        // Find program data section named .tohost to detect if the elf file is riscv-tests
        self.tohost_addr = analyzer
            .find_tohost_addr(&program_data_section_headers, &string_table_section_headers)
            .unwrap_or(0);

        // Creates symbol - virtual address mapping
        if !string_table_section_headers.is_empty() {
            let entries = analyzer.read_symbol_entries(&header, &symbol_table_section_headers);
            // Assuming symbols are in the first string table section.
            // @TODO: What if symbol can be in the second or later string table sections?
            let map = analyzer.create_symbol_map(&entries, string_table_section_headers[0]);
            for (key, value) in map {
                self.symbol_map.insert(key, value);
            }
        }

        // Detected whether the elf file is riscv-tests.
        // Setting up CPU and Memory depending on it.
        if self.tohost_addr != 0 {
            self.is_test = true;
            self.cpu.get_mut_mmu().init_memory(TEST_MEMORY_CAPACITY);
        } else {
            self.is_test = false;
            self.cpu.get_mut_mmu().init_memory(PROGRAM_MEMORY_CAPACITY);
        }

        for sh in program_data_section_headers {
            let sh_addr = sh.sh_addr;
            let sh_offset = sh.sh_offset as usize;
            let sh_size = sh.sh_size as usize;
            if sh_addr >= 0x80000000 && sh_offset > 0 && sh_size > 0 {
                for j in 0..sh_size {
                    if self
                        .cpu
                        .get_mut_mmu()
                        .store_phys_u8(sh_addr + j as u64, analyzer.read_byte(sh_offset + j))
                        .is_err()
                    {
                        panic!(
                            "Program doesn't fit in memory: 0x{:016x}",
                            sh_addr + j as u64
                        );
                    }
                }
            }
        }

        self.cpu.update_pc(header.e_entry as i64);
    }

    /// Loads symbols of program and adds them to `symbol_map`.
    ///
    /// # Arguments
    /// * `content` Program binary
    /// # Panics
    /// Panics on non-Elf files
    pub fn load_program_for_symbols(&mut self, content: Vec<u8>) {
        let analyzer = ElfAnalyzer::new(content);

        assert!(analyzer.validate(), "This file does not seem ELF file");

        let header = analyzer.read_header();
        let section_headers = analyzer.read_section_headers(&header);

        //let mut program_data_section_headers = vec![];
        let mut symbol_table_section_headers = vec![];
        let mut string_table_section_headers = vec![];

        for sh in &section_headers {
            match sh.sh_type {
                //1 => program_data_section_headers.push(sh),
                2 => symbol_table_section_headers.push(sh),
                3 => string_table_section_headers.push(sh),
                _ => {}
            }
        }

        // Creates symbol - virtual address mapping
        if !string_table_section_headers.is_empty() {
            let entries = analyzer.read_symbol_entries(&header, &symbol_table_section_headers);
            // Assuming symbols are in the first string table section.
            // @TODO: What if symbol can be in the second or later string table sections?
            let map = analyzer.create_symbol_map(&entries, string_table_section_headers[0]);
            for (key, value) in map {
                self.symbol_map.insert(key, value);
            }
        }
    }

    /// Sets up filesystem. Use this method if program (e.g. Linux) uses
    /// filesystem. This method is expected to be called up to only once.
    ///
    /// # Arguments
    /// * `content` File system content binary
    pub fn setup_filesystem(&mut self, content: Vec<u8>) {
        self.cpu.get_mut_mmu().init_disk(content);
    }

    /// Sets up device tree. The emulator has default device tree configuration.
    /// If you want to override it, use this method. This method is expected to
    /// to be called up to only once.
    ///
    /// # Arguments
    /// * `content` DTB content binary
    pub fn setup_dtb(&mut self, content: &[u8]) {
        self.cpu.get_mut_mmu().init_dtb(content);
    }

    /// Enables or disables page cache optimization.
    /// Page cache optimization is experimental feature.
    /// See [`Mmu`](./mmu/struct.Mmu.html) for the detail.
    ///
    /// # Arguments
    /// * `enabled`
    pub fn enable_page_cache(&mut self, enabled: bool) {
        self.cpu.get_mut_mmu().enable_page_cache(enabled);
    }

    /// Returns mutable reference to `Terminal`.
    pub fn get_mut_terminal(&mut self) -> &mut Box<dyn Terminal> {
        self.cpu.get_mut_terminal()
    }

    /// Returns immutable reference to `Cpu`.
    #[must_use]
    pub const fn get_cpu(&self) -> &Cpu {
        &self.cpu
    }

    /// Returns mutable reference to `Cpu`.
    pub const fn get_mut_cpu(&mut self) -> &mut Cpu {
        &mut self.cpu
    }

    /// Returns a virtual address corresponding to symbol strings
    ///
    /// # Arguments
    /// * `s` Symbol strings
    #[must_use]
    pub fn get_addredd_of_symbol(&self, s: &String) -> Option<u64> {
        self.symbol_map.get(s).copied()
    }
}

#[cfg(test)]
mod test_emulator {
    use super::*;
    use crate::terminal::DummyTerminal;

    fn create_emu() -> Emulator {
        Emulator::new(Box::new(DummyTerminal::new()))
    }

    #[test]
    fn initialize() {
        let _emu = create_emu();
    }

    #[test]
    #[ignore]
    const fn run() {}

    #[test]
    #[ignore]
    const fn run_program() {}

    #[test]
    #[ignore]
    const fn run_test() {}

    #[test]
    #[ignore]
    const fn tick() {}

    #[test]
    #[ignore]
    const fn setup_program() {}

    #[test]
    #[ignore]
    const fn load_program_for_symbols() {}

    #[test]
    #[ignore]
    const fn setup_filesystem() {}

    #[test]
    #[ignore]
    const fn setup_dtb() {}

    #[test]
    #[ignore]
    const fn update_xlen() {}

    #[test]
    #[ignore]
    const fn enable_page_cache() {}

    #[test]
    #[ignore]
    const fn get_addredd_of_symbol() {}
}
