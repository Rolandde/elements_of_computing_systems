//! The kernel implementation of the Hack [computer][architecture::Computer] described in The Elements of Computing Systems book.
//! 
//! # Note on `no_std`
//! The kernel does not depend on the Rust `std` library, but uses the `alloc` crate. This means the system using this needs to be able to allocate memory on the heap. Allocation was necessary as stack overflow errors happened with the memory. A 32K memory of 16 [Bit][crate::seq_logic::Bit] registers has 524288 [Bit][crate::seq_logic::Bit]s. Each Bit is a bool (1 byte), so the stack has to hold more than 4 megabytes. This crashes on my Windows 10 machine (curious how much stack Ubuntu provides).

#![no_std]
extern crate alloc;

pub mod chapter1_gates;
pub mod chapter2_arithmetic;
pub mod chapter3_sequenctial_logic;
pub mod chapter5_computer_architecture;

pub use chapter1_gates as gates;
pub use chapter2_arithmetic as arithmetic;
pub use chapter3_sequenctial_logic as seq_logic;
pub use chapter5_computer_architecture as architecture;

/// Convenience function to get `bool` arrays for specific numbers.
///
/// # Examples
/// ```
/// use hack_kernel::from_i16;
/// assert_eq!(
///     from_i16(0),
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
/// );
/// assert_eq!(
///     from_i16(1),
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
/// );
/// assert_eq!(
///     from_i16(-1),
///     [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
/// );
/// ```
///
pub fn from_i16(a: i16) -> [bool; 16] {
    [
        a < 0,
        a & (i16::pow(2, 14)) != 0,
        a & (i16::pow(2, 13)) != 0,
        a & (i16::pow(2, 12)) != 0,
        a & (i16::pow(2, 11)) != 0,
        a & (i16::pow(2, 10)) != 0,
        a & (i16::pow(2, 9)) != 0,
        a & (i16::pow(2, 8)) != 0,
        a & (i16::pow(2, 7)) != 0,
        a & (i16::pow(2, 6)) != 0,
        a & (i16::pow(2, 5)) != 0,
        a & (i16::pow(2, 4)) != 0,
        a & (i16::pow(2, 3)) != 0,
        a & (i16::pow(2, 2)) != 0,
        a & (i16::pow(2, 1)) != 0,
        a & (i16::pow(2, 0)) != 0,
    ]
}

pub use architecture::{Computer, Debugger, Rom32K, Rom32KWriter};
