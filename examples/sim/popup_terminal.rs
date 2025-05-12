use crate::nonblocknoecho::NonblockNoEcho;
use simmerv::terminal::Terminal;
use std::io::{self, Stdout, Write};

/// Popup `Terminal` used for desktop program.
pub struct PopupTerminal {
    input: NonblockNoEcho,
}

impl PopupTerminal {
    pub fn new() -> Self {
        Self {
            input: NonblockNoEcho::new(false), // Don't catch ctrl-C  ... for now
        }
    }
}

impl Terminal for PopupTerminal {
    fn put_byte(&mut self, value: u8) {
        print!("{}", value as char);
    }

    #[allow(clippy::expect_used, clippy::unwrap_used)]
    fn get_input(&mut self) -> u8 {
        let stdout: Stdout = io::stdout();
        stdout.lock().flush().unwrap();
        self.input.get_key().unwrap_or_default()
    }

    // Wasm specific methods. No use.
    fn put_input(&mut self, _value: u8) {}

    fn get_output(&mut self) -> u8 {
        0
    }
}
