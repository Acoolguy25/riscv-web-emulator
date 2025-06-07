// src/device/rtc.rs

#![allow(clippy::cast_possible_truncation)]

// Base address of your 64-bit RTC
const RTC_BASE: u64 = 0x1000_2000;

/// A read-only RTC device that hands you the current UNIX time in ns.
pub struct RTC;

impl RTC {
    #[must_use]
    pub fn new() -> Self {
        RTC
    }

    /// Load one byte from the 64-bit time value.
    #[allow(clippy::cast_possible_wrap)]
    pub fn load(&mut self, address: u64) -> u8 {
        // Grab the current time in nanoseconds:
        let now_ns = get_time_ns();
        // Figure out which byte they want:
        let byte_index = (address - RTC_BASE) as usize;
        ((now_ns >> (byte_index * 8)) & 0xff) as u8
    }

    /// No writes—just ignore them.
    pub fn store(&mut self, _address: u64, _value: u8) {}
}

// Helper to pick the right source of “now”:
#[inline]
fn get_time_ns() -> u64 {
    #[cfg(target_arch = "wasm32")]
    {
        // Directly import JS’s Date.now() → millisecond accuracy,
        // multiply to get nanoseconds.  This is a flat host import,
        // it does *not* re-enter any of your wasm exports.
        (js_sys::Date::now() * 1e6) as u64
    }
    #[cfg(not(target_arch = "wasm32"))]
    {
        use std::time::{SystemTime, UNIX_EPOCH};
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
    }
}
