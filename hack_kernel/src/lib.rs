//! The kernel implementation of the Hack [computer][architecture::Computer] described in The Elements of Computing Systems book.
//! 
//! # Note on `no_std`
//! The kernel does not depend on the Rust `std` library, but uses the `alloc` crate. This means the system using this needs to be able to allocate memory on the heap. Allocation was necessary as stack overflow errors happened with the memory. A 32K memory of 16 [Bit][crate::seq_logic::Bit] registers has 524288 [Bit][crate::seq_logic::Bit]s. Each Bit is a bool (1 byte), so the stack has to hold more than 4 megabytes. This crashes on my Windows 10 machine (curious how much stack Ubuntu provides).
//! 
//! # Note on cheating with memory
//! The 32K [memory][architecture::DataMemory] is much too slow to be used in the [Computer]. It takes more than 10 seconds to scan through the screen with the release build. This is because a real hardware chip works in parallel, but the software emulated hardware does not. To read or write to the emulated memory, each register has to be visited on at a time. To stress this, specifying a single address still leads to every address being visited. This is an unavoidable outcome of following the rules of the game: building the emulated computer hardware from a single chip.
//! 
//! There is no point in dying on the hill of principle, so there exists [architecture::CheatingDataMemory]. It is this memory which is used in [Computer] and [Rom32K]. It cheats by emulating the memory as one vector of registers. The address is converted to the index of the register. A read or write operation visits only a single register, which is way faster than visiting them all.

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

/// Convenience function to get `bool` arrays from specific numbers.
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
    // 1 followed by 15 0s
    let x: i16 = -32768;
    [
        (a & x) != 0,
        ((a << 1) & x) != 0,
        ((a << 2) & x) != 0,
        ((a << 3) & x) != 0,
        ((a << 4) & x) != 0,
        ((a << 5) & x) != 0,
        ((a << 6) & x) != 0,
        ((a << 7) & x) != 0,
        ((a << 8) & x) != 0,
        ((a << 9) & x) != 0,
        ((a << 10) & x) != 0,
        ((a << 11) & x) != 0,
        ((a << 12) & x) != 0,
        ((a << 13) & x) != 0,
        ((a << 14) & x) != 0,
        ((a << 15) & x) != 0,
    ]
}

/// Convenience function to get 15 element bool array from a number.
/// 
/// `i16` has one extra bit of information. The most significant bit will be ignored. This means that input should be equal to or greater than 0.
///
/// # Examples
/// ```
/// use hack_kernel::from_i15;
/// assert_eq!(
///     from_i15(0),
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
/// );
/// assert_eq!(
///     from_i15(1),
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true]
/// );
/// assert_eq!(
///     from_i15(32767),
///     [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
/// );
/// ```
///
pub fn from_i15(a: i16) -> [bool; 15] {
    // 1 followed by 15 0s
    let x: i16 = -32768;
    [
        ((a << 1) & x) != 0,
        ((a << 2) & x) != 0,
        ((a << 3) & x) != 0,
        ((a << 4) & x) != 0,
        ((a << 5) & x) != 0,
        ((a << 6) & x) != 0,
        ((a << 7) & x) != 0,
        ((a << 8) & x) != 0,
        ((a << 9) & x) != 0,
        ((a << 10) & x) != 0,
        ((a << 11) & x) != 0,
        ((a << 12) & x) != 0,
        ((a << 13) & x) != 0,
        ((a << 14) & x) != 0,
        ((a << 15) & x) != 0,
    ]
}

pub use architecture::{Computer, Debugger, Rom32K, Rom32KWriter};
