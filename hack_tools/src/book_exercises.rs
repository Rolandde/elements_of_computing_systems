//! Exercises from the The Elements of Computing Systems book.
//!
//! These exercises could not be done (easily) in the [hack_kernel] module, as the solution depends on Rust `std`.
//!

use crate::{Bit15, Bit16, Debugger};

/// Add 2 and 3 and store result to RAM\[0\].
///
/// The hack machine code was given to test that the computer functions properly.
///
/// # Solution
/// ```
/// use hack_tools::book_exercises::*;
/// assert_eq!(chapter5_add(), "0000000000000101".parse().unwrap());
/// ```
pub fn chapter5_add() -> Bit16 {
    const INSTRUCTIONS: &'static str = "0000000000000010
        1110110000010000
        0000000000000011
        1110000010010000
        0000000000000000
        1110001100001000";
    let rom = crate::hack_io::write_rom_from_buffer(INSTRUCTIONS.as_bytes());
    let mut computer = hack_kernel::Computer::new(rom);
    for _ in 0..6 {
        computer.cycle(false);
    }
    Debugger::new(&mut computer).read_memory("000000000000000".parse().unwrap())
}

/// Write the max number to RAM\[2\], with the two input numbers at RAM\[0\] and RAM\[1\]
///
/// The hack machine code was given to test that the computer functions properly.
///
/// # Solution
/// ```
/// use hack_tools::book_exercises::*;
/// use hack_tools::Bit16;
/// assert_eq!(chapter5_max(1.into(), 2.into()), 2.into());
/// assert_eq!(chapter5_max(2.into(), 1.into()), 2.into());
/// assert_eq!(chapter5_max(0.into(), 0.into()), 0.into());
/// assert_eq!(chapter5_max(Bit16::from(-1), Bit16::from(-2)), Bit16::from(-1));
/// ```
pub fn chapter5_max(a: Bit16, b: Bit16) -> Bit16 {
    const INSTRUCTIONS: &'static str = "0000000000000000
    1111110000010000
    0000000000000001
    1111010011010000
    0000000000001010
    1110001100000001
    0000000000000001
    1111110000010000
    0000000000001100
    1110101010000111
    0000000000000000
    1111110000010000
    0000000000000010
    1110001100001000
    0000000000001110
    1110101010000111";
    let rom = crate::hack_io::write_rom_from_buffer(INSTRUCTIONS.as_bytes());
    let mut computer = hack_kernel::Computer::new(rom);
    let mut debugger = Debugger::new(&mut computer);
    debugger.write_memory(Bit15::from(0), a);
    debugger.write_memory(Bit15::from(1), b);
    // Machine code loops infinitely from the last line
    while debugger.read_cpu_counter() != Bit16::from(15) {
        debugger.computer().cycle(false)
    }
    debugger.read_memory(Bit15::from(2))
}
