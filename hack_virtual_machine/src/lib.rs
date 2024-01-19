use std::convert::Into;

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    Add,
    Subtract,
    Negative,
    Equal,
    GreaterThan,
    LessThan,
    BitAnd,
    BitOr,
    BitNot,
    Goto(String),
    If(String),
    Label(String),
    Pop(Segment, u16),
    Push(Segment, u16),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Segment {
    Argument,
    Local,
    Static,
    Constant,
    This,
    That,
    Pointer,
    Temp,
}

impl std::str::FromStr for Segment {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "argument" => Ok(Segment::Argument),
            "local" => Ok(Segment::Local),
            "static" => Ok(Segment::Static),
            "constant" => Ok(Segment::Constant),
            "this" => Ok(Segment::This),
            "that" => Ok(Segment::That),
            "pointer" => Ok(Segment::Pointer),
            "temp" => Ok(Segment::Temp),
            _ => Err(()),
        }
    }
}

/// Virtual machine stack addition.
pub fn add() -> [Assembly; 9] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::DPlusM).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack subtraction.
pub fn sub() -> [Assembly; 9] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack negation.
pub fn neg() -> [Assembly; 4] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::MinusM).into(),
    ]
}

/// Virtual machine equality
pub fn eq() -> [Assembly; 24] {
    // For the comments, assume stack pointer at memory 0 points to 3
    // The two numbers to compare at memory 1(X) and 2(Y)
    [
        ReservedSymbols::SP.into(),                    // A = 0 (stack pointer)
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] (3, top of stack)
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(), // A = 2
        CCommand::new_dest(CDest::D, CComp::M).into(), // D = M[2] (Y)
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(), // A = 1
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(), // M[1] = X - Y
        CCommand::new_dest(CDest::D, CComp::A).into(), // D = 1
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::M, CComp::D).into(), // M[0] = 1, stack pointer is at subtraction result
        CCommand::new_dest(CDest::D, CComp::M).into(), // D = X - Y
        ACommand::Symbol("EQUAL".to_string()).into(),  // @EQUAL
        CCommand::new_jump(CComp::D, CJump::Equal).into(), // Jump to EQUAL if D is 0, otherwise not equal
        ReservedSymbols::SP.into(),                        // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] (1, where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::Zero).into(), // M[1] = 0
        ACommand::Symbol("EQUAL_DONE".to_string()).into(), // Jump to finishing equal assembly
        CCommand::new_jump(CComp::Zero, CJump::Jump).into(), // Always jump to finishing assembly
        Assembly::Label("EQUAL".to_string()),          // Code for equality
        ReservedSymbols::SP.into(),                    // A at stack pointer (second of stack)
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] (1, where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::MinumOne).into(), // Second of stack is -1 (true)
        Assembly::Label("EQUAL_DONE".to_string()),     // Code for finishing up equality
        ReservedSymbols::SP.into(),                    // A at stack pointer (second of stack)
        CCommand::new_dest(CDest::M, CComp::APlusOne).into(), // A at stack pointer, but now top of stack
    ]
}

/// Errors during VM functioning
#[derive(Debug)]
pub enum Error {
    /// The command has too few, too many, or wrong type of arguments
    InvalidArgs(u16),
    /// Upstream IO error.
    Io(std::io::Error),
    /// The command is not part of the VM spec
    UnknownCommand(u16),
    /// The segement is not part of the VM spec
    UnknownSegment(u16),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidArgs(line) => {
                write!(f, "wrong arg number or type on line {}", line)
            }
            Self::Io(e) => write!(f, "cannot read: {}", e),
            Self::UnknownCommand(line) => write!(f, "unknown command on line {}", line),
            Self::UnknownSegment(line) => write!(f, "unknown segment on line {}", line),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidArgs(_) => None,
            Self::Io(e) => Some(e),
            Self::UnknownCommand(_) => None,
            Self::UnknownSegment(_) => None,
        }
    }
}

impl std::convert::From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

pub mod reader;

#[cfg(test)]
mod vm_tests {
    use super::*;
    use std::convert::TryFrom;

    #[test]
    fn test_add() {
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&add()).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 3.into()); // Stack pointer past the two numbers
        d.write_memory(1.into(), 10.into()); // 10 is the first number to add
        d.write_memory(2.into(), 100.into()); // 100 is the second number to add
        let i = i16::try_from(add().len()).unwrap();
        while d.read_cpu_counter() != i.into() {
            d.computer().cycle(false);
        }
        assert_eq!(d.read_memory(1.into()), 110.into());
        assert_eq!(d.read_memory(0.into()), 2.into());
    }

    #[test]
    fn test_sub() {
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&sub()).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 3.into()); // Stack pointer past the two numbers
        d.write_memory(1.into(), 10.into()); // 10 is the minuend
        d.write_memory(2.into(), 100.into()); // 100 is the subtrahend
        let i = i16::try_from(add().len()).unwrap();
        while d.read_cpu_counter() != i.into() {
            d.computer().cycle(false);
        }
        assert_eq!(d.read_memory(1.into()), (-90).into());
        assert_eq!(d.read_memory(0.into()), 2.into());
    }

    #[test]
    fn test_neg() {
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&neg()).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 2.into()); // Stack pointer is past the number to negate
        d.write_memory(1.into(), (-10).into());
        let i = i16::try_from(add().len()).unwrap();
        while d.read_cpu_counter() != i.into() {
            d.computer().cycle(false);
        }
        assert_eq!(d.read_memory(1.into()), 10.into());
        assert_eq!(d.read_memory(0.into()), 2.into());
    }
}
