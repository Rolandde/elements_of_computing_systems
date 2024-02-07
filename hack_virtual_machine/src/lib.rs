use hack_assembler::parts::ReservedSymbols;

/// Memory address at which the start pointer starts
pub const STACK_START: i16 = 256;

/// Memory address at which the heap starts
pub const HEAP_START: i16 = 2048;

/// This virtual register will hold the popped value
pub const MEM_POP: ReservedSymbols = ReservedSymbols::R14;

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
    Pop(Segment),
    Push(Segment),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Segment {
    Argument(i16),
    Local(i16),
    Static(i16),
    Constant(i16),
    This(i16),
    That(i16),
    // The pointer segment only has two positions
    PointerThis,
    PointerThat,
    // The temp segment has 8 defined positions
    Temp0,
    Temp1,
    Temp2,
    Temp3,
    Temp4,
    Temp5,
    Temp6,
    Temp7,
    Temp8,
}

/// Errors during VM functioning
#[derive(Debug)]
pub enum Error {
    /// The command has too few, too many, or wrong type of arguments
    InvalidArgs(usize),
    /// Upstream IO error.
    Io(std::io::Error),
    /// The command is not part of the VM spec
    UnknownCommand(usize),
    /// The segement is not part of the VM spec
    UnknownSegment(usize),
    /// Segment index is out of bounds
    OutOfBoundsIndex(usize),
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
            Self::OutOfBoundsIndex(line) => write!(f, "out of bounds index on line {}", line),
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
            Self::OutOfBoundsIndex(_) => None,
        }
    }
}

impl std::convert::From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

pub mod arithmetic;
pub mod memory;
pub mod reader;
