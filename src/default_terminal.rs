use crate::terminal::{Terminal};
#[allow(unused_imports)]
use crate::terminal;

/// Standard `Terminal`.
pub struct DefaultTerminal {
    input_data: Vec<u8>,
    output_data: Vec<u8>,
}

impl Default for DefaultTerminal {
    fn default() -> Self {
        Self::new()
    }
}

impl DefaultTerminal {
    #[must_use]
    pub fn new() -> Self {
        Self {
            input_data: vec![],
            output_data: vec![],
        }
    }
}

impl Terminal for DefaultTerminal {
    fn put_byte(&mut self, value: u8) {
        // terminal::log_to_browser!("idx {}", self.get_idx());
        self.output_data.push(value);
    }

    fn get_input(&mut self) -> u8 {
        if self.input_data.is_empty() {
            0
        } else {
            self.input_data.remove(0)
        }
    }

    fn put_input(&mut self, value: u8) {
        self.input_data.push(value);
    }

    fn get_output(&mut self) -> u8 {
        if self.output_data.is_empty() {
            0
        } else {
            // terminal::log_to_browser!("output w idx {}", self.idx);
            self.output_data.remove(0)
        }
    }

}
