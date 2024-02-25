//! The supremly stacked virtual machine.
//!
//! # Equal, greater than, less than arithmetic commands
//! These are special, because they have jump statments within them. The book didn't hint at them being anything special and I couldn't think of a way of doing it without jumping. The jumps addresses are marked with labels. This means that the assembly code for these VM commands can only be inserted once. Using absolute addresses would allow you to insert it multiple times, but then the VM would have to keep track of them. My approach was to stick with labels and insert each assembly block once during compilation. The VM ensures that the R13 register is set to the next command that needs to be executed once the comparison operation has finished.
//!
//! # Wherefore impl Trait
//! [VirtualMachine] dumps assembly into a container that implements `extend`. I originally had that as a `Vec`. This makes sense for dumping all assembly lines into memory. But then I wanted to have an iterator that gets vm commands in chunks and throws out assembly in chunks. That means I need to pop out elements from the front of the collection. `VedDeque` does that nice. So now I have a impl Trait.

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
    file_name: String,
    command_lines: i16,
    translated: Vec<AssemblyLine>,
    func: Option<String>, // What function is the VM currently going through
    call_count: usize, // How many call have been made within the function (resets between functions)
}

impl VirtualMachine {
    /// Create a new virtual machine for a specific `.vm` file.
    ///
    /// The `file_name` can be changed during compilation, must not include the `.vm` extension, and is assumed to be a valid file name.
    pub fn new(file_name: String) -> Self {
        Self {
            file_name,
            command_lines: 0,
            translated: Vec::new(),
            func: None,
            call_count: 0,
        }
    }

    /// Sets up stack and common calls.
    ///
    /// Call this immediatly after createring the VM and before running [VirtualMachine::compile]. The stack won't be there if you don't.
    pub fn init(&mut self, assembly: &mut impl std::iter::Extend<AssemblyLine>) {
        self.translated.extend([
            AssemblyLine::Comment("Set stack pointer".to_string()),
            AssemblyLine::Assembly(ACommand::Address(STACK_START).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(ReservedSymbols::SP.into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
            AssemblyLine::Assembly(ACommand::Symbol("START".to_string()).into()), // Starting a program requires function calls, which are for the next chapter
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        self.init_equlity(arithmetic::eq(), "EQ".to_string());
        self.init_equlity(arithmetic::gt(), "GT".to_string());
        self.init_equlity(arithmetic::lt(), "LT".to_string());

        self.translated // This can be removed once function calls are implemented and the root function is called
            .push(AssemblyLine::Assembly(Assembly::Label("START".to_string())).into());

        for a in &self.translated {
            if a.is_command() {
                self.command_lines += 1;
            }
        }
        assembly.extend(self.translated.drain(..));
    }

    /// Compile a VM line into assembly.
    ///
    /// It is possible that no assembly will be produced by this call. Calling `pop const 42` does nothing. Future optimizers might take a VM line and not compile it until the next ones are seen. (I have no intention of going down the optimizer road).
    pub fn compile(
        &mut self,
        vm_command: &Command,
        assembly: &mut impl std::iter::Extend<AssemblyLine>,
    ) {
        match vm_command {
            Command::Add => {
                self.add_comment("ADD".to_string());
                for a in arithmetic::add() {
                    self.translated.push(a.into())
                }
            }
            Command::Subtract => {
                self.add_comment("SUB".to_string());
                for a in arithmetic::sub() {
                    self.translated.push(a.into())
                }
            }
            Command::Negative => {
                self.add_comment("NEG".to_string());
                for a in arithmetic::neg() {
                    self.translated.push(a.into())
                }
            }
            Command::Equal => self.call_equality("EQ".to_string()),
            Command::GreaterThan => self.call_equality("GT".to_string()),
            Command::LessThan => self.call_equality("LT".to_string()),
            Command::BitAnd => {
                self.add_comment("AND".to_string());
                for a in arithmetic::and() {
                    self.translated.push(a.into())
                }
            }
            Command::BitOr => {
                self.add_comment("OR".to_string());
                for a in arithmetic::or() {
                    self.translated.push(a.into())
                }
            }
            Command::BitNot => {
                self.add_comment("NOT".to_string());
                for a in arithmetic::not() {
                    self.translated.push(a.into())
                }
            }
            Command::Push(s) => match s.into() {
                UsefulSegment::Pointer(r, i) => {
                    self.add_comment(format!("PUSH {r} {i}"));
                    for a in memory::push_pointer(r, i) {
                        self.translated.push(a.into())
                    }
                }
                UsefulSegment::Const(c) => {
                    self.add_comment(format!("PUSH CONST {c}"));
                    for a in memory::push_constant(c) {
                        self.translated.push(a.into())
                    }
                }
                UsefulSegment::Static(i) => {
                    self.add_comment(format!("PUSH STATIC {}.{i}", self.file_name));
                    for a in memory::push_static(&self.file_name, i) {
                        self.translated.push(a.into())
                    }
                }
                UsefulSegment::Value(r) => {
                    self.add_comment(format!("PUSH {r}"));
                    for a in memory::push_value(r) {
                        self.translated.push(a.into())
                    }
                }
            },
            Command::Pop(s) => match s.into() {
                UsefulSegment::Pointer(r, i) => {
                    self.add_comment(format!("POP {r} {i}"));
                    for a in memory::pop_pointer(r, i) {
                        self.translated.push(a.into())
                    }
                }
                UsefulSegment::Const(c) => {
                    self.add_comment(format!("POP CONST {c} . . . WHY?!?"));
                }
                UsefulSegment::Static(i) => {
                    self.add_comment(format!("POP STATIC {}.{i}", self.file_name));
                    for a in memory::pop_static(&self.file_name, i) {
                        self.translated.push(a.into())
                    }
                }
                UsefulSegment::Value(r) => {
                    self.add_comment(format!("POP {r}"));
                    for a in memory::pop_value(r) {
                        self.translated.push(a.into())
                    }
                }
            },
            Command::Goto(l) => {
                self.add_comment(format!("GOTO {l}"));
                for a in branching::goto(self.generate_label(l)) {
                    self.translated.push(a.into())
                }
            }
            Command::GotoIf(l) => {
                self.add_comment(format!("IF-GOTO {l}"));
                for a in branching::if_goto(self.generate_label(l)) {
                    self.translated.push(a.into())
                }
            }
            Command::Label(l) => {
                self.add_comment(format!("LABEL {l}"));
                self.translated.push(AssemblyLine::Assembly(Assembly::Label(
                    self.generate_label(l),
                )))
            }
            Command::Function(_, _) => panic!("no function support"),
            Command::Call(_, _) => panic!("no call support"),
            Command::Return => panic!("no return suppport"),
        };
        for a in &self.translated {
            if a.is_command() {
                self.command_lines += 1;
            }
        }

        assembly.extend(self.translated.drain(..));
    }

    /// Call after the last command has been compiled to flush out any remaining assembly lines.
    ///
    /// In case the virtual machine has buffered lines for optimization. As there is none (and I don't plan to do any), this does nothing, but good to code in the assumption in case I suddenly change my mind.
    pub fn flush(&mut self, _assembly: &mut impl std::iter::Extend<AssemblyLine>) {}

    /// Add an infinate loop.
    ///
    /// Good practice to add one at the end of assembly to prevent the counter from going of the edge and looping back.
    pub fn infinate_loop(&mut self, assembly: &mut impl std::iter::Extend<AssemblyLine>) {
        self.add_comment("Infinite loop at end of program".into());
        self.translated.extend([
            AssemblyLine::Assembly(Assembly::Label("ENDLOOP".to_string()).into()),
            AssemblyLine::Assembly(ACommand::Symbol("ENDLOOP".to_string()).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        for a in &self.translated {
            if a.is_command() {
                self.command_lines += 1;
            }
        }

        assembly.extend(self.translated.drain(..));
    }

    /// The virtual machine is now getting commands from a new file.
    ///
    /// The file name provides scope for labels in the assembly code.
    pub fn update_file_name(&mut self, new_name: String) {
        self.file_name = new_name;
    }

    fn init_equlity(&mut self, assembly: [Assembly; 24], label: String) {
        self.translated.push(Assembly::Label(label).into());
        for a in assembly {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                MEM_ARITH.into(),
                "return address set by VM before equality call".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::A, CComp::M).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);
    }

    fn call_equality(&mut self, symbol: String) {
        // + 6 is how many commands there are below. Don't change command without changing this addition.
        let return_address = self.command_lines + 6;
        self.translated.extend([
            AssemblyLine::Comment(format!("calling {symbol}")),
            AssemblyLine::AssemblyComment(
                ACommand::Address(return_address).into(),
                "return address calculated by VM".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(MEM_ARITH.into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
            AssemblyLine::Assembly(ACommand::Symbol(symbol).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);
    }

    fn add_comment(&mut self, comment: String) {
        self.translated.push(AssemblyLine::Comment(comment));
    }

    fn generate_label(&self, label: &str) -> String {
        match &self.func {
            None => format!("{}${label}", self.file_name),
            Some(s) => format!("{}.{s}${label}", self.file_name),
        }
    }
}

/// The commands the virtual machine supports
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
    GotoIf(String),
    Label(String),
    Pop(Segment),
    Push(Segment),
    Function(String, i16),
    Call(String, i16),
    Return,
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
            Self::Goto(s) => write!(f, "goto {s}"),
            Self::GotoIf(s) => write!(f, "if-goto {s}"),
            Self::Label(s) => write!(f, "label {s}"),
            Self::Function(s, i) => write!(f, "function {s} {i}"),
            Self::Call(s, i) => write!(f, "call {s} {i}"),
            Self::Return => write!(f, "return"),
        }
    }
}

/// The segment of the push and pop command.
///
/// the `pointer` and `temp` segment only have 2 or 8 possible offsents, respecivly. Rather than doing `Segment::Temp(i16)` and checking/assuming validity, only the valid offsets can be created. [reader::Reader] causes an error if invalid offsets are encountered and everything downstream can now be happy without any assumptions.
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
///
/// Should this be part of the [hack_assembler] crate. Sigh, probably. But it's a lot of work without any immediate benefit.
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
    /// Label or function name is invalid (does not begin with number, and is alphanumberic, _, ., and :)
    InvalidLabelFunc(usize),
    /// Upstream IO error.
    Io(std::io::Error),
    /// Segment index is out of bounds
    OutOfBoundsIndex(usize),
    /// The command is not part of the VM spec
    UnknownCommand(usize),
    /// The segement is not part of the VM spec
    UnknownSegment(usize),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidArgs(line) => {
                write!(f, "wrong arg number or type on line {}", line)
            }
            Self::InvalidLabelFunc(line) => {
                write!(f, "invalid label or function name on line {}", line)
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
            Self::InvalidLabelFunc(_) => None,
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

/// Obtained by converting from [Segment]. This enum mirrors the functions in [memory], making matching the [VirtualMachine::compile] cleaner.
enum UsefulSegment {
    Pointer(ReservedSymbols, i16),
    Const(i16),
    Static(i16),
    Value(ReservedSymbols),
}

impl std::convert::From<&Segment> for UsefulSegment {
    fn from(value: &Segment) -> Self {
        match value {
            Segment::Argument(i) => Self::Pointer(ReservedSymbols::ARG, *i),
            Segment::Local(i) => Self::Pointer(ReservedSymbols::LCL, *i),
            Segment::Static(i) => Self::Static(*i),
            Segment::Constant(i) => Self::Const(*i),
            Segment::This(i) => Self::Pointer(ReservedSymbols::THIS, *i),
            Segment::That(i) => Self::Pointer(ReservedSymbols::THAT, *i),
            Segment::PointerThis => Self::Value(ReservedSymbols::R3),
            Segment::PointerThat => Self::Value(ReservedSymbols::R4),
            Segment::Temp0 => Self::Value(ReservedSymbols::R5),
            Segment::Temp1 => Self::Value(ReservedSymbols::R6),
            Segment::Temp2 => Self::Value(ReservedSymbols::R7),
            Segment::Temp3 => Self::Value(ReservedSymbols::R8),
            Segment::Temp4 => Self::Value(ReservedSymbols::R9),
            Segment::Temp5 => Self::Value(ReservedSymbols::R10),
            Segment::Temp6 => Self::Value(ReservedSymbols::R11),
            Segment::Temp7 => Self::Value(ReservedSymbols::R12),
        }
    }
}

pub mod arithmetic;
pub mod branching;
pub mod memory;
pub mod reader;

#[cfg(test)]
mod book_tests {
    use super::*;

    const SIMPLE_ADD: &'static str = "// Pushes and adds two constants.
push constant 7
push constant 8
add";

    const STACK_TEST: &'static str = "// Executes a sequence of arithmetic and logical operations
// on the stack. 
push constant 17
push constant 17
eq
push constant 17
push constant 16
eq
push constant 16
push constant 17
eq
push constant 892
push constant 891
lt
push constant 891
push constant 892
lt
push constant 891
push constant 891
lt
push constant 32767
push constant 32766
gt
push constant 32766
push constant 32767
gt
push constant 32766
push constant 32766
gt
push constant 57
push constant 31
push constant 53
add
push constant 112
sub
neg
and
push constant 82
or
not";

    const SEGMENT_TEST: &'static str =
        "// Executes pop and push commands using the virtual memory segments.
push constant 10
pop local 0
push constant 21
push constant 22
pop argument 2
pop argument 1
push constant 36
pop this 6
push constant 42
push constant 45
pop that 5
pop that 2
push constant 510
pop temp 6
push local 0
push that 5
add
push argument 1
sub
push this 6
push this 6
add
sub
push temp 6
add";

    const POINTER_TEST: &'static str = "// Executes pop and push commands using the 
// pointer, this, and that segments.
push constant 3030
pop pointer 0
push constant 3040
pop pointer 1
push constant 32
pop this 2
push constant 46
pop that 6
push pointer 0
push pointer 1
add
push this 2
sub
push that 6
add";

    const STATIC_TEST: &'static str = "// Executes pop and push commands using the static segment.
push constant 111
push constant 333
push constant 888
pop static 8
pop static 3
pop static 1
push static 3
push static 1
sub
push static 8
add";

    fn compile(vm_lines: &str) -> Vec<Assembly> {
        let mut al = Vec::new();
        let mut vm = VirtualMachine::new("file".to_string());
        vm.init(&mut al);
        for c in reader::CommandLines::new(vm_lines.as_bytes()) {
            vm.compile(&c.unwrap(), &mut al);
        }
        vm.flush(&mut al);
        vm.infinate_loop(&mut al);

        let mut ass = Vec::new();
        for l in al {
            match l {
                AssemblyLine::Assembly(a) => ass.push(a),
                AssemblyLine::AssemblyComment(a, _) => ass.push(a),
                AssemblyLine::Comment(_) => {}
            }
        }

        ass
    }

    #[test]
    fn test_simple_add() {
        let ass = compile(SIMPLE_ADD);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        let mut i = 0;
        // Number of cycles from book
        while i < 60 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 257.into());
        assert_eq!(d.read_memory(256.into()), 15.into());
    }

    #[test]
    fn test_stack() {
        let ass = compile(STACK_TEST);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        let mut i = 0;
        // Number of cycles from book
        while i < 1000 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 266.into());
        assert_eq!(d.read_memory(256.into()), (-1).into());
        assert_eq!(d.read_memory(257.into()), 0.into());
        assert_eq!(d.read_memory(258.into()), 0.into());
        assert_eq!(d.read_memory(259.into()), 0.into());
        assert_eq!(d.read_memory(260.into()), (-1).into());
        assert_eq!(d.read_memory(261.into()), 0.into());
        assert_eq!(d.read_memory(262.into()), (-1).into());
        assert_eq!(d.read_memory(263.into()), 0.into());
        assert_eq!(d.read_memory(264.into()), 0.into());
        assert_eq!(d.read_memory(265.into()), (-91).into());
    }

    #[test]
    fn test_pointer() {
        let ass = compile(POINTER_TEST);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        let mut i = 0;
        // Number of cycles from book
        while i < 450 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 257.into());
        assert_eq!(d.read_memory(256.into()), 6084.into());
        assert_eq!(d.read_memory(3.into()), 3030.into());
        assert_eq!(d.read_memory(4.into()), 3040.into());
        assert_eq!(d.read_memory(3032.into()), 32.into());
        assert_eq!(d.read_memory(3046.into()), 46.into());
    }

    #[test]
    fn test_static() {
        let ass = compile(STATIC_TEST);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        let mut i = 0;
        // Number of cycles from book
        while i < 200 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 257.into());
        assert_eq!(d.read_memory(16.into()), 888.into());
        assert_eq!(d.read_memory(17.into()), 333.into());
        assert_eq!(d.read_memory(18.into()), 111.into());
        assert_eq!(d.read_memory(256.into()), 1110.into());
    }

    #[test]
    fn test_segment() {
        let ass = compile(SEGMENT_TEST);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        // No initialization of segments pointers by VM after Chapter 7. The values are from the BasicTest.tst file
        d.write_memory(1.into(), 300.into());
        d.write_memory(2.into(), 400.into());
        d.write_memory(3.into(), 3000.into());
        d.write_memory(4.into(), 3010.into());

        let mut i = 0;
        // Number of cycles from book
        while i < 600 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 257.into());
        assert_eq!(d.read_memory(256.into()), 472.into());
        assert_eq!(d.read_memory(300.into()), 10.into());
        assert_eq!(d.read_memory(401.into()), 21.into());
        assert_eq!(d.read_memory(402.into()), 22.into());
        assert_eq!(d.read_memory(3006.into()), 36.into());
        assert_eq!(d.read_memory(3012.into()), 42.into());
        assert_eq!(d.read_memory(3015.into()), 45.into());
        assert_eq!(d.read_memory(11.into()), 510.into());
    }
}
