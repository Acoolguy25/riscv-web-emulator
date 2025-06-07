// src/device/log.rs

#![allow(clippy::cast_possible_truncation)]

use crate::terminal;

/// A write-only Console device that prints to console
pub struct Sys {
    message: String,
}

impl Sys {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            message: String::new(),
        }
    }

    pub fn store(&mut self, _address: u64, value: u8) {
        let c = value as char;
        if (c == '\n' && self.message.is_empty()) || c == '\r'{
            return;
        }
        if c == '\n' {
            terminal::log_to_browser_color!("{}",    
                    "color: white; background: black; text-shadow:
                    0 1px 0 #000,
                    1px 0 0 #000,
                    0 -1px 0 #000,
                    -1px 0 0 #000,
                    1px 1px 0 #000,
                    -1px -1px 0 #000,
                    -1px 1px 0 #000,
                    1px -1px 0 #000,
                    2px 0px 0 #000,
                    -2px 0px 0 #000,
                    0px 2px 0 #000,
                    0px -2px 0 #000;",
                self.message);

            self.message = String::new();
        }
        else{
            self.message.push(c);
        }
    }

    pub const fn load(&mut self, _address: u64) -> u8 {
        0
    }
}

impl Default for Sys {
    fn default() -> Self {
        Self::new()
    }
}