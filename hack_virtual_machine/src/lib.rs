//! The supremly stacked virtual machine.
//!
//! # Equal, greater than, less than arithmetic commands
//! These are special, because they have jump statments within them. The book didn't hint at them being anything special and I couldn't think of a way of doing it without jumping. The jumps addresses are marked with labels. This means that the assembly code for these VM commands can only be inserted once. Using absolute addresses would allow you to insert it multiple times, but then the VM would have to keep track of them. My approach was to stick with labels and insert each assembly block once during compilation. The VM ensures that the R13 register is set to the next command that needs to be executed once the comparison operation has finished.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Memory address at which the start pointer starts
pub const STACK_START: i16 = 256;

/// Memory address at which the heap starts
pub const HEAP_START: i16 = 2048;

/// This virtual register holds the address to return to after arithmetic comparisons
pub const MEM_ARITH: ReservedSymbols = ReservedSymbols::R13;

/// This virtual register will hold the popped value
pub const MEM_POP: ReservedSymbols = ReservedSymbols::R14;

/// The stacked virtual machine
pub struct VirtualMachine {
    command_lines: i16,
    translated: Vec<AssemblyLine>,
}

impl VirtualMachine {
    pub fn new() -> Self {
        Self {
            command_lines: 0,
            translated: Vec::new(),
        }
    }

    pub fn init(&mut self) -> &[AssemblyLine] {
        self.translated.extend([
            AssemblyLine::Comment("Set stack pointer".to_string()),
            AssemblyLine::Assembly(ACommand::Address(STACK_START).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(ReservedSymbols::SP.into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
        ]);

        // Equality assembly
        self.translated.extend([
            AssemblyLine::Comment("equality".to_string()),
            Assembly::Label("EQ".to_string()).into(),
        ]);
        for a in arithmetic::eq() {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                MEM_ARITH.into(),
                "set by the VM before jump to this assembly block".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        // Greater than assembly
        self.translated.extend([
            AssemblyLine::Comment("greater than".to_string()),
            Assembly::Label("GT".to_string()).into(),
        ]);
        for a in arithmetic::gt() {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                MEM_ARITH.into(),
                "set by the VM before jump to this assembly block".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        // Less than assembly
        self.translated.extend([
            AssemblyLine::Comment("less than".to_string()),
            Assembly::Label("LT".to_string()).into(),
        ]);
        for a in arithmetic::lt() {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                MEM_ARITH.into(),
                "set by the VM before jump to this assembly block".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        for a in &self.translated {
            if a.is_command() {
                self.command_lines += 1;
            }
        }
        &self.translated
    }

    pub fn compile(&mut self, vm_command: &Command) -> &[AssemblyLine] {
        self.translated.clear();
        match vm_command {
            Command::Add => {
                for a in arithmetic::add() {
                    self.translated.push(a.into())
                }
            }
            Command::GreaterThan => {
                let return_address = self.command_lines + 6;
                let gt = [
                    AssemblyLine::Comment("calling greater than".to_string()),
                    AssemblyLine::AssemblyComment(
                        ACommand::Address(return_address).into(),
                        "return address calculated by VM".to_string(),
                    ),
                    AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
                    AssemblyLine::Assembly(MEM_ARITH.into()),
                    AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
                    AssemblyLine::Assembly(ACommand::Symbol("GT".to_string()).into()),
                    AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
                ];
            }
            _ => panic!("AHHHHHHHHHHHHHHHHHHH"),
        };
        &self.translated
    }
}

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
    // Goto(String),
    // If(String),
    // Label(String),
    Pop(Segment),
    Push(Segment),
}

impl std::fmt::Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "add"),
            Self::Subtract => write!(f, "sub"),
            Self::Negative => write!(f, "neg"),
            Self::Equal => write!(f, "eq"),
            Self::GreaterThan => write!(f, "gt"),
            Self::LessThan => write!(f, "lt"),
            Self::BitAnd => write!(f, "and"),
            Self::BitOr => write!(f, "or"),
            Self::BitNot => write!(f, "not"),
            Self::Pop(s) => write!(f, "pop {s}"),
            Self::Push(s) => write!(f, "push {s}"),
        }
    }
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
}

impl std::fmt::Display for Segment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Argument(i) => write!(f, "argument {i}"),
            Self::Local(i) => write!(f, "local {i}"),
            Self::Static(i) => write!(f, "static {i}"),
            Self::Constant(i) => write!(f, "constant {i}"),
            Self::This(i) => write!(f, "this {i}"),
            Self::That(i) => write!(f, "that {i}"),
            Self::PointerThis => write!(f, "pointer 0"),
            Self::PointerThat => write!(f, "pointer 1"),
            Self::Temp0 => write!(f, "temp 0"),
            Self::Temp1 => write!(f, "temp 1"),
            Self::Temp2 => write!(f, "temp 2"),
            Self::Temp3 => write!(f, "temp 3"),
            Self::Temp4 => write!(f, "temp 4"),
            Self::Temp5 => write!(f, "temp 5"),
            Self::Temp6 => write!(f, "temp 6"),
            Self::Temp7 => write!(f, "temp 7"),
        }
    }
}

/// VM translation produces assembly alongside very helpful comments
#[derive(Debug, PartialEq, Eq)]
pub enum AssemblyLine {
    Comment(String),
    AssemblyComment(Assembly, String),
    Assembly(Assembly),
}

impl AssemblyLine {
    /// Will this assembly line yield machine instructions. See [Assembly::is_command()].
    pub fn is_command(&self) -> bool {
        match self {
            Self::Comment(_) => false,
            Self::AssemblyComment(a, _) => a.is_command(),
            Self::Assembly(a) => a.is_command(),
        }
    }
}

impl std::fmt::Display for AssemblyLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Comment(s) => write!(f, "//{s}"),
            Self::AssemblyComment(a, s) => write!(f, "{a} //{s}"),
            Self::Assembly(a) => write!(f, "{a}"),
        }
    }
}

impl std::convert::From<Assembly> for AssemblyLine {
    fn from(value: Assembly) -> Self {
        Self::Assembly(value)
    }
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
