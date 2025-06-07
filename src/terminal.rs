/// Emulates terminal. It holds input/output data in buffer
/// transferred to/from `Emulator`.
pub trait Terminal {
    /// Puts an output ascii byte data to output buffer.
    /// The data is expected to be read by user program via `get_output()`
    /// and be displayed to user.
    fn put_byte(&mut self, value: u8);

    /// Gets an output ascii byte data from output buffer.
    /// This method returns zero if the buffer is empty.
    fn get_output(&mut self) -> u8;

    /// Puts an input ascii byte data to input buffer.
    /// The data is expected to be read by `Emulator` via `get_input()`
    /// and be handled.
    fn put_input(&mut self, data: u8);

    /// Gets an input ascii byte data from input buffer.
    /// Used by `Emulator`.
    fn get_input(&mut self) -> u8;

}

/// For the test or whatever.
pub struct DummyTerminal {}

impl Default for DummyTerminal {
    fn default() -> Self {
        Self::new()
    }
}

impl DummyTerminal {
    #[must_use]
    pub const fn new() -> Self {
        Self {}
    }
}

impl Terminal for DummyTerminal {
    fn put_byte(&mut self, _value: u8) {}
    fn get_input(&mut self) -> u8 {
        0
    }
    fn put_input(&mut self, _value: u8) {}
    fn get_output(&mut self) -> u8 {
        0
    }
}

/// Logs a formatted message to the browser console (like println!).
#[macro_export]
macro_rules! log_to_browser {
    ($($arg:tt)*) => {{
        use web_sys::console;
        let s = format!($($arg)*);
        console::log_1(&s.into());
    }};
}

#[macro_export]
macro_rules! log_to_browser_color {
    ($fmt:expr, $css:expr, $($arg:tt)*) => {{
        use web_sys::console;
        use web_sys::wasm_bindgen::JsValue;
        // Same as JS: "%c" pattern, CSS string, formatted text
        console::log_2(
            &JsValue::from_str(&format!("%c{}", format!($fmt, $($arg)*))),
            &JsValue::from_str($css),
        );
    }};
    ($fmt:expr, $css:expr) => {{
        use web_sys::console;
        use web_sys::wasm_bindgen::JsValue;
        console::log_2(
            &JsValue::from_str(&format!("%c{}", $fmt)),
            &JsValue::from_str($css),
        );
    }};
}

pub use crate::log_to_browser;
pub use crate::log_to_browser_color;