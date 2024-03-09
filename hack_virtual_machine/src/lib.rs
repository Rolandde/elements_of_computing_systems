//! The supremly stacked virtual machine.
//!
//! # Equal, greater than, less than arithmetic commands
//! These are special, because they have jump statments within them. The book didn't hint at them being anything special and I couldn't think of a way of doing it without jumping. The jumps addresses are marked with labels. This means that the assembly code for these VM commands can only be inserted once. Using absolute addresses would allow you to insert it multiple times, but then the VM would have to keep track of them. My approach was to stick with labels and insert each assembly block once during compilation. The VM ensures that the R13 register is set to the next command that needs to be executed once the comparison operation has finished.
//!
//! # Wherefore impl Trait
//! [VirtualMachine] dumps assembly into a container that implements `extend`. I originally had that as a `Vec`. This makes sense for dumping all assembly lines into memory. But then I wanted to have an iterator that gets vm commands in chunks and throws out assembly in chunks. That means I need to pop out elements from the front of the collection. `VedDeque` does that nice. So now I have a impl Trait.
//!
//! # Do I need a file name?
//! Yes, but the book is confusing about it. The file name is necessary because labels and access to static segments are file specific. Writing `label foo` or `static pop 3` in two different files translates to different assembly code. The confusion comes when dealing with `function` commands. My initial assumption was that `function bar` in a file `foo.vm` generates a assembly label `(foo.bar)`. However, the excersises in Chapter 8 have `function foo.bar` in the file `foo.vm`. This leads me to believe the jack compiler generates those unique function names and the VM doesn't have to deal with it. I have removed the use of the file name from translating the `function` command.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Memory address at which the start pointer starts
const STACK_START: i16 = 256;

/// This virtual register holds the address to return to after arithmetic comparisons
const RETURN_ADDRESS: ReservedSymbols = ReservedSymbols::R13;

/// This virtual register will hold the popped value
const MEM_POP: ReservedSymbols = ReservedSymbols::R14;

/// Where are number of args for calling function stored
const N_ARGS_PLUS_5: ReservedSymbols = ReservedSymbols::R14;

/// The stacked virtual machine
pub struct VirtualMachine {
    file_name: String,
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
            AssemblyLine::Assembly(ACommand::Symbol("Sys.init".to_string()).into()), // The VM expects this function somewhere
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

        self.init_equlity(arithmetic::eq(), "EQ".to_string());
        self.init_equlity(arithmetic::gt(), "GT".to_string());
        self.init_equlity(arithmetic::lt(), "LT".to_string());
        self.init_function_local_vars();
        self.init_call();
        self.init_return();

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
            Command::Function(s, l) => {
                self.func = Some(s.to_string());
                let return_address = format!("{s}$$LOCAL_VAR_INIT");
                self.add_comment(format!("FUNCTION {s} {l}"));
                // `function::local_vars` expects the number of local variables in the D register
                // And return address in return register
                self.translated.extend([
                    AssemblyLine::Assembly(Assembly::Label(s.to_string())),
                    AssemblyLine::Assembly(ACommand::Symbol(return_address.clone()).into()),
                    AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
                    AssemblyLine::Assembly(RETURN_ADDRESS.into()),
                    AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
                    AssemblyLine::Assembly(ACommand::Address(*l).into()),
                    AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
                    AssemblyLine::Assembly(ACommand::Symbol("LOCAL_VARS".to_string()).into()),
                    AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
                    AssemblyLine::Assembly(Assembly::Label(return_address)),
                ]);
            }
            Command::Call(s, args) => {
                self.call_call(s, *args);
            }
            Command::Return => {
                self.add_comment("RETURN".to_string());
                self.func = None;
                self.translated.extend([
                    AssemblyLine::Assembly(ACommand::Symbol("RETURN".to_string()).into()),
                    AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
                ])
            }
        };

        assembly.extend(self.translated.drain(..));
    }

    /// Call after the last command has been compiled to flush out any remaining assembly lines.
    ///
    /// In case the virtual machine has buffered lines for optimization. As there is none (and I don't plan to do any), this does nothing, but good to code in the assumption in case I suddenly change my mind.
    pub fn flush(&mut self, _assembly: &mut impl std::iter::Extend<AssemblyLine>) {}

    /// Add an infinate loop.
    ///
    /// Good practice to add one at the end of assembly to prevent the counter from going off the edge and looping back.
    pub fn infinate_loop(&mut self, assembly: &mut impl std::iter::Extend<AssemblyLine>) {
        self.add_comment("Infinite loop at end of program".into());
        self.translated.extend([
            AssemblyLine::Assembly(ACommand::Symbol("ENDLOOP".to_string()).into()),
            AssemblyLine::Assembly(Assembly::Label("ENDLOOP".to_string()).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);

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
                RETURN_ADDRESS.into(),
                "return address set by VM before equality call".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::A, CComp::M).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);
    }

    fn call_equality(&mut self, symbol: String) {
        let counter = self.get_counter();
        let label = format!("{symbol}_RETURN{counter}");
        self.translated.extend([
            AssemblyLine::Comment(format!("calling {symbol}")),
            AssemblyLine::AssemblyComment(
                ACommand::Symbol(label.clone()).into(),
                "label after jump to equality".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(RETURN_ADDRESS.into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
            AssemblyLine::Assembly(ACommand::Symbol(symbol).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
            AssemblyLine::Assembly(Assembly::Label(label)),
        ]);
    }

    // After setting local variables on the stack, jump to beginning of function
    fn init_function_local_vars(&mut self) {
        self.add_comment("local var initialization for all functions".to_string());
        for a in crate::function::local_vars() {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                RETURN_ADDRESS.into(),
                "return address set by VM before jump to this block".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::A, CComp::M).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);
    }

    fn init_call(&mut self) {
        self.add_comment("call assembly used by all".to_string());
        self.translated
            .push(Assembly::Label("CALL".to_string()).into());
        for a in crate::function::call_stack() {
            self.translated.push(a.into())
        }
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                RETURN_ADDRESS.into(),
                "return address set by VM before jump to this block".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::A, CComp::M).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
        ]);
    }

    fn call_call(&mut self, s: &str, args: i16) {
        self.add_comment(format!("CALL {s} {args}"));
        let counter = self.get_counter();
        let ret_str = match &self.func {
            None => format!("{}$$ret.{counter}", self.file_name),
            Some(f) => format!("{f}$$ret.{counter}"),
        };
        self.translated.extend([
            AssemblyLine::AssemblyComment(
                ACommand::Address(args + 5).into(),
                "number of args + 5".to_string(),
            ),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(ACommand::Reserved(N_ARGS_PLUS_5).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
            AssemblyLine::Assembly(ACommand::Symbol(s.to_string()).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(ACommand::Reserved(RETURN_ADDRESS).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::M, CComp::D).into()),
            AssemblyLine::Assembly(ACommand::Symbol(ret_str.clone()).into()),
            AssemblyLine::Assembly(CCommand::new_dest(CDest::D, CComp::A).into()),
            AssemblyLine::Assembly(ACommand::Symbol("CALL".to_string()).into()),
            AssemblyLine::Assembly(CCommand::new_jump(CComp::One, CJump::Jump).into()),
            AssemblyLine::Assembly(Assembly::Label(ret_str)),
        ]);
    }

    fn init_return(&mut self) {
        self.translated
            .push(Assembly::Label("RETURN".to_string()).into());
        self.add_comment("return assembly used by all".to_string());
        for a in crate::function::return_from_func() {
            self.translated.push(a.into())
        }
    }

    fn add_comment(&mut self, comment: String) {
        self.translated.push(AssemblyLine::Comment(comment));
    }

    fn generate_label(&self, label: &str) -> String {
        match &self.func {
            None => format!("{}${label}", self.file_name),
            Some(s) => format!("{s}${label}"),
        }
    }

    fn get_counter(&mut self) -> usize {
        let r = self.call_count;
        self.call_count += 1;
        r
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
    /// Cannot define a function here
    InvalidFunction(usize),
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
            Self::InvalidFunction(line) => {
                write!(f, "invalid function defenition on line {}", line)
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
            Self::InvalidFunction(_) => None,
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
pub mod function;
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

    const BASIC_LOOP: &'static str =
        "// Computes the sum 1 + 2 + ... + n and pushes the result onto
// the stack. The value n is given in argument[0], which must be 
// initialized by the caller of this code.

    push constant 0    
    pop local 0         // sum = 0
label LOOP
    push argument 0     
    push local 0
    add
    pop local 0	        // sum = sum + n
    push argument 0
    push constant 1
    sub
    pop argument 0      // n--
    push argument 0
    if-goto LOOP        // if n > 0, goto LOOP
    push local 0        // else, pushes sum to the stack's top";

    const FIBONACCI: &'static str =
        "// Puts the first n elements of the Fibonacci series in the memory,
    // starting at address addr. n and addr are given in argument[0] and
    // argument[1], which must be initialized by the caller of this code.
    
        push argument 1         // sets THAT, the base address of the
        pop pointer 1           // that segment, to argument[1]
        push constant 0         // sets the series' first and second
        pop that 0              // elements to 0 and 1, respectively       
        push constant 1   
        pop that 1              
        push argument 0         // sets n, the number of remaining elements
        push constant 2         // to be computed to argument[0] minus 2,
        sub                     // since 2 elements were already computed.
        pop argument 0          
    
    label LOOP
        push argument 0
        if-goto COMPUTE_ELEMENT // if n > 0, goto COMPUTE_ELEMENT
        goto END                // otherwise, goto END
    
    label COMPUTE_ELEMENT
        // that[2] = that[0] + that[1]
        push that 0
        push that 1
        add
        pop that 2
        // THAT += 1 (updates the base address of that)
        push pointer 1
        push constant 1
        add
        pop pointer 1 
        // updates n-- and loops          
        push argument 0
        push constant 1
        sub
        pop argument 0          
        goto LOOP
    
    label END";

    const SIMPLE_FUNCTION: &'static str = "// Performs a simple calculation and returns the result.
    // argument[0] and argument[1] must be set by the caller of this code.
    function SimpleFunction.test 2
        push local 0
        push local 1
        add
        not
        push argument 0
        add
        push argument 1
        sub
        return";

    const NESTED_CALL: &'static str = "// Calls Sys.main() and stores a return value in temp 1.
    // Does not return (enters infinite loop).
    // The VM implementation starts running this function, by default.
    function Sys.init 0
        push constant 4000	// tests that THIS and THAT are handled correctly
        pop pointer 0
        push constant 5000
        pop pointer 1
        call Sys.main 0
        pop temp 1
        label LOOP
        goto LOOP
        return
    
    // Sets locals 1, 2 and 3 to some values. Leaves locals 0 and 4 unchanged, 
    // to test that the 'function' VM command initliazes them to 0 (the test 
    // script sets them to -1 before this code starts running).
    // Calls Sys.add12(123) and stores the return value (should be 135) in temp 0.
    // Returns local 0 + local 1 + local 2 + local 3 + local 4 (should be 456), to 
    // confirm that locals were not mangled by the function call.
    function Sys.main 5
        push constant 4001
        pop pointer 0
        push constant 5001
        pop pointer 1
        push constant 200
        pop local 1
        push constant 40
        pop local 2
        push constant 6
        pop local 3
        push constant 123
        call Sys.add12 1
        pop temp 0
        push local 0
        push local 1
        push local 2
        push local 3
        push local 4
        add
        add
        add
        add
        return
    
    // Returns (argument 0) + 12.
    function Sys.add12 0
        push constant 4002
        pop pointer 0
        push constant 5002
        pop pointer 1
        push argument 0
        push constant 12
        add
        return";

    // Utility function that initializes the VM, makes a barebone `Sys.init` call, finishes up the VM
    fn compile(vm_lines: &str) -> Vec<Assembly> {
        let mut al = Vec::new();
        let mut vm = VirtualMachine::new("file".to_string());
        vm.init(&mut al);
        vm.compile(&&&Command::Function("Sys.init".to_string(), 0), &mut al);
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

    #[test]
    fn test_basic_loop() {
        let ass = compile(BASIC_LOOP);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 256.into());
        d.write_memory(1.into(), 300.into());
        d.write_memory(2.into(), 400.into());
        d.write_memory(400.into(), 5.into()); // 1 + 2 + 3 + 4

        let mut i = 0;
        // Number of cycles from book
        while i < 600 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 257.into());
        assert_eq!(d.read_memory(256.into()), 15.into());
    }

    #[test]
    fn test_fibonacci() {
        let ass = compile(FIBONACCI);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 256.into());
        d.write_memory(1.into(), 300.into());
        d.write_memory(2.into(), 400.into());
        d.write_memory(400.into(), 6.into()); // 0 + 1 + 1 + 2 + 3 + 5
        d.write_memory(401.into(), 3000.into());

        let mut i = 0;
        // Number of cycles from book
        while i < 1100 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(3000.into()), 0.into());
        assert_eq!(d.read_memory(3001.into()), 1.into());
        assert_eq!(d.read_memory(3002.into()), 1.into());
        assert_eq!(d.read_memory(3003.into()), 2.into());
        assert_eq!(d.read_memory(3004.into()), 3.into());
        assert_eq!(d.read_memory(3005.into()), 5.into());
    }

    #[test]
    fn test_simple_function() {
        let ass = compile(SIMPLE_FUNCTION);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        // Run the first 5 instructions, which set the stack pointer, and then overwrite them
        for _ in 0..5 {
            d.computer().cycle(false);
        }

        d.write_memory(0.into(), 317.into());
        d.write_memory(1.into(), 317.into());
        d.write_memory(2.into(), 310.into());
        d.write_memory(3.into(), 3000.into());
        d.write_memory(4.into(), 4000.into());
        d.write_memory(317.into(), 42.into()); // Testing if LCL segment is set to 0
        d.write_memory(318.into(), 42.into());
        d.write_memory(310.into(), 1234.into());
        d.write_memory(311.into(), 37.into());
        d.write_memory(312.into(), 1000.into()); // The frame
        d.write_memory(313.into(), 305.into());
        d.write_memory(314.into(), 300.into());
        d.write_memory(315.into(), 3010.into());
        d.write_memory(316.into(), 4010.into());

        let mut i = 0;
        // Number of cycles from book
        while i < 300 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 311.into());
        assert_eq!(d.read_memory(1.into()), 305.into());
        assert_eq!(d.read_memory(2.into()), 300.into());
        assert_eq!(d.read_memory(3.into()), 3010.into());
        assert_eq!(d.read_memory(4.into()), 4010.into());
        assert_eq!(d.read_memory(310.into()), 1196.into());
    }

    // I've changed the VM code for this function, adding a return statement to Sys.init
    #[test]
    fn test_nested_calls() {
        let mut al = Vec::new();
        let mut vm = VirtualMachine::new("Sys".to_string());
        vm.init(&mut al);
        for c in reader::CommandLines::new(NESTED_CALL.as_bytes()) {
            vm.compile(&c.unwrap(), &mut al);
        }
        vm.flush(&mut al);
        let mut ass = Vec::new();
        for l in al {
            match l {
                AssemblyLine::Assembly(a) => ass.push(a),
                AssemblyLine::AssemblyComment(a, _) => ass.push(a),
                AssemblyLine::Comment(_) => {}
            }
        }

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        // Run the first 5 instructions, which set the stack pointer, and then overwrite them
        for _ in 0..5 {
            d.computer().cycle(false);
        }

        d.write_memory(0.into(), 261.into());
        d.write_memory(1.into(), 261.into());
        d.write_memory(2.into(), 257.into());

        let mut i = 0;
        // Number of cycles from book
        while i < 4000 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 261.into());
    }
}

// Functions are hard. I had to simplify some book tests to figure out where exactly they were failing
#[cfg(test)]
mod my_tests {
    use super::*;

    #[test]
    fn test_simple_nested() {
        let code = "// Calls Sys.main() and stores a return value in temp 1.
    // Does not return (enters infinite loop).
    // The VM implementation starts running this function, by default.
    function Sys.init 0
        push constant 4000	// tests that THIS and THAT are handled correctly
        pop pointer 0
        push constant 5000
        pop pointer 1
        call Sys.main 0
        pop temp 1
        label LOOP
        goto LOOP
        return

    function Sys.main 0
        push constant 4001
        return  
        ";
        let mut al = Vec::new();
        let mut vm = VirtualMachine::new("Sys".to_string());
        vm.init(&mut al);
        for c in reader::CommandLines::new(code.as_bytes()) {
            vm.compile(&c.unwrap(), &mut al);
        }
        vm.flush(&mut al);
        let mut ass = Vec::new();
        for l in al {
            match l {
                AssemblyLine::Assembly(a) => ass.push(a),
                AssemblyLine::AssemblyComment(a, _) => ass.push(a),
                AssemblyLine::Comment(_) => {}
            }
        }

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        // Run the first 5 instructions, which set the stack pointer, and then overwrite them
        for _ in 0..5 {
            d.computer().cycle(false);
        }

        d.write_memory(0.into(), 261.into());
        d.write_memory(1.into(), 261.into());
        d.write_memory(2.into(), 250.into());

        let mut i = 0;
        // Number of cycles from book
        while i < 4000 {
            d.computer().cycle(false);
            i += 1;
        }

        assert_eq!(d.read_memory(0.into()), 261.into());
    }
}
