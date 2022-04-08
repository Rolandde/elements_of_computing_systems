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
    let rom = crate::hack_io::write_rom_from_buffer(TWO_PLUS_THREE.as_bytes());
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
    let rom = crate::hack_io::write_rom_from_buffer(PICK_MAX.as_bytes());
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

/// Assemble the 2+3 machine code
/// 
/// # Examples
/// ```
/// use hack_tools::book_exercises::*;
/// use hack_tools::hack_io::Writer;
/// let mut machine_code = Writer::new(Vec::new());
/// chapter6_assemble_add(&mut machine_code)?;
/// assert_eq!(TWO_PLUS_THREE.as_bytes(), machine_code.as_ref());
/// # Ok::<(), hack_tools::Error>(())
/// ```
pub fn chapter6_assemble_add<W>(write_to: &mut crate::hack_io::Writer<W>) -> Result<(), crate::Error>
where
    W: std::io::Write,
{
    let asm = b"
        @2
        D=A
        @3
        D=D+A
        @0
        M=D
    ";

    for bit16 in crate::assembly::assemble_from_bytes(&asm[..])? {
        write_to.write_instruction(&bit16?)?;
    }

    Ok(())
}

/// Assemble the max machine code (no labels)
/// 
/// # Examples
/// ```
/// use hack_tools::book_exercises::*;
/// use hack_tools::hack_io::Writer;
/// let mut machine_code = Writer::new(Vec::new());
/// chapter6_assemble_max_no_label(&mut machine_code)?;
/// assert_eq!(PICK_MAX.as_bytes(), machine_code.as_ref());
/// # Ok::<(), hack_tools::Error>(())
/// ```
pub fn chapter6_assemble_max_no_label<W>(write_to: &mut crate::hack_io::Writer<W>) -> Result<(), crate::Error>
where
    W: std::io::Write,
{
    let asm = b"
        @0
        D=M
        @1
        D=D-M
        @10
        D;JGT
        @1
        D=M
        @12
        0;JMP
        @0
        D=M
        @2
        M=D
        @14
        0;JMP
    ";

    for bit16 in crate::assembly::assemble_from_bytes(&asm[..])? {
        write_to.write_instruction(&bit16?)?;
    }

    Ok(())
}

/// Assemble the max machine code (with labels)
/// 
/// # Examples
/// ```
/// use hack_tools::book_exercises::*;
/// use hack_tools::hack_io::Writer;
/// let mut machine_code = Writer::new(Vec::new());
/// chapter6_assemble_max_label(&mut machine_code)?;
/// assert_eq!(PICK_MAX.as_bytes(), machine_code.as_ref());
/// # Ok::<(), hack_tools::Error>(())
/// ```
pub fn chapter6_assemble_max_label<W>(write_to: &mut crate::hack_io::Writer<W>) -> Result<(), crate::Error>
where
    W: std::io::Write,
{
    let asm = b"
        // Computes R2 = max(R0, R1)  (R0,R1,R2 refer to RAM[0],RAM[1],RAM[2])

        @R0
        D=M              // D = first number
        @R1
        D=D-M            // D = first number - second number
        @OUTPUT_FIRST
        D;JGT            // if D>0 (first is greater) goto output_first
        @R1
        D=M              // D = second number
        @OUTPUT_D
        0;JMP            // goto output_d
        (OUTPUT_FIRST)
        @R0             
        D=M              // D = first number
        (OUTPUT_D)
        @R2
        M=D              // M[2] = D (greatest number)
        (INFINITE_LOOP)
        @INFINITE_LOOP
        0;JMP            // infinite loop
    ";

    for bit16 in crate::assembly::assemble_from_bytes(&asm[..])? {
        write_to.write_instruction(&bit16?)?;
    }

    Ok(())
}

/// Machine code to add 2 and 3 and store result to RAM\[0\].
pub const TWO_PLUS_THREE: &'static str = "0000000000000010
1110110000010000
0000000000000011
1110000010010000
0000000000000000
1110001100001000
";

/// Machine code to Write the max number to RAM\[2\], with the two input numbers at RAM\[0\] and RAM\[1\]
pub const PICK_MAX: &'static str = "0000000000000000
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
1110101010000111
";
