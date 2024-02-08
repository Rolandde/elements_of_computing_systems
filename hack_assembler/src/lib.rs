//! Converts `.asm` assembly format to `.hack` machine instructions format. You probably want to use [assemble_from_bytes] or [assemble_from_file].
//!
//! [Assembly] is at the core of parsing. Use the [io::AssemblyLines] iterator created by [io::Reader] to convert asm into nice enums.
//!
//! The [Assembler] is the core process, taking a single [Assembly] line at a time and alongside the symbol table, producing [hack_interface::Bit16] machine instructions. [FirstPass] creates a [SymbolTable]. [SecondPass] is an iterator that wraps [Assembler].
//!
//! [FirstPass] has to see all assembly lines, because [Assembly::Label] can be used before it is defined. If you know know there are no labels in the `.asm` file, skip the first pass and use [SymbolTable::empty] for the second pass. Note that the danger is that everything will work just fine with a [SecondPass] even if labels are present in your assembly code. This will result in wrong machine code, as an A-command with a label (`@END`) will be misinterpreted as a new address in RAM rather than an instruction position in the ROM. There are ways (that either increase code complexity or decrease efficiency) to prevent this type of bug, but the current solution is to always run first pass, unless you know it is not needed.

pub mod io;
pub mod parts;
pub mod pass;
use parts::{ACommand, CCommand};
use pass::SecondPassTrusted;
pub use pass::{FirstPass, SecondPass, SymbolTable};

/// The way to keep an assembly line in memory
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Assembly {
    /// A line with only whitespace and/or comments
    Empty,
    /// `A` command setting the `A` register
    A(ACommand),
    /// `C` command doing a computation and optionally setting registers and/or jumping
    C(CCommand),
    /// A label recording the position of the next command in the assembly
    Label(String),
}

impl std::fmt::Display for Assembly {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, ""),
            Self::A(a) => write!(f, "{a}"),
            Self::C(c) => write!(f, "{c}"),
            Self::Label(s) => write!(f, "({s})"),
        }
    }
}

/// Convert one [Assembly] line at a time into machine code.
///
/// [SymbolTable] must be created by [FirstPass] if labels are in the assembly file.
pub struct Assembler {
    symbol_table: SymbolTable,
    variable_symbol_count: i16,
}

impl Assembler {
    pub fn new(symbol_table: SymbolTable) -> Self {
        Self {
            symbol_table,
            variable_symbol_count: 16,
        }
    }

    /// Do a second pass from a buffer.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::{Assembler, Assembly, SymbolTable};
    /// use hack_assembler::parts::ACommand;
    /// let st = SymbolTable::empty();
    /// let mut assembler = Assembler::new(st);
    /// assert_eq!(
    ///     assembler.pass_line(&Assembly::A(ACommand::Address(42))),
    ///     Some(42.into())
    /// );
    /// assert_eq!(
    ///     assembler.pass_line(&Assembly::Empty),
    ///     None
    /// );
    /// ```
    pub fn pass_line(&mut self, assembly: &Assembly) -> Option<hack_interface::Bit16> {
        match assembly {
            Assembly::Empty => None,
            Assembly::A(a_cmd) => Some(self.assemble_a_command(a_cmd)),
            Assembly::C(c_cmd) => Some((*c_cmd).into()),
            Assembly::Label(_) => None,
        }
    }

    fn assemble_a_command(&mut self, a: &ACommand) -> hack_interface::Bit16 {
        match a {
            ACommand::Address(b) => (*b).into(),
            ACommand::Reserved(r) => (*r).into(),
            ACommand::Symbol(s) => match self.symbol_table.get(&s) {
                Some(b) => hack_interface::Bit16::from(b),
                None => {
                    let current_address = self.variable_symbol_count.into();
                    self.symbol_table.insert(s.clone(), current_address);
                    self.variable_symbol_count += 1;
                    current_address.into()
                }
            },
        }
    }
}

/// Two pass assembly from a byte source.
///
/// Returns [SecondPass] iterator that gives machine instructions.
///
/// # Examples
/// ```
/// let asm = b"
/// // This keeps adding 1 to the RAM address 16 forever.
/// (FOREVER)
/// @i
/// M=M+1
/// @FOREVER
/// 0;JMP
/// ";
/// let second_pass_iter = hack_assembler::assemble_from_bytes(&asm[..])?;
/// // Neat way of converting `Vec<Result>` to `Result<Vec>`
/// let machine_code = second_pass_iter.collect::<Result<Vec<_>, _>>()?;
/// assert_eq!(machine_code.len(), 4);
/// assert_eq!(machine_code[0], 16.into());
/// assert_eq!(machine_code[1], "1111110111001000".parse()?);
/// assert_eq!(machine_code[2], 0.into());
/// assert_eq!(machine_code[3], "1110101010000111".parse()?);
/// # Ok::<(), hack_interface::Error>(())
/// ```
pub fn assemble_from_bytes(
    from: &[u8],
) -> Result<SecondPass<io::AssemblyLines<&[u8]>>, hack_interface::Error> {
    let symbol_table = FirstPass::from_buffer(from)?;
    let iter = io::Reader::new(from).assembly_lines();
    Ok(SecondPass::new(iter, symbol_table))
}

/// Two pass assembly from a `.asm` file.
///
/// Returns a scary looking [SecondPass] iterator that returns machine instructions.
///
/// # Examples
/// ```
/// let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
/// d.push("resources/test/example.asm");
/// let second_pass_iter = hack_assembler::assemble_from_file(d)?;
/// // Neat way of converting `Vec<Result>` to `Result<Vec>`
/// let machine_code = second_pass_iter.collect::<Result<Vec<_>, _>>()?;
/// assert_eq!(machine_code.len(), 4);
/// assert_eq!(machine_code[0], 16.into());
/// assert_eq!(machine_code[1], "1111110111001000".parse()?);
/// assert_eq!(machine_code[2], 0.into());
/// assert_eq!(machine_code[3], "1110101010000111".parse()?);
/// # Ok::<(), hack_interface::Error>(())
/// ```
pub fn assemble_from_file<P: AsRef<std::path::Path>>(
    path: P,
) -> Result<SecondPass<io::AssemblyLines<std::io::BufReader<std::fs::File>>>, hack_interface::Error>
{
    let mut f = std::fs::File::open(path.as_ref())?;
    let mut buf = std::io::BufReader::new(f);
    let symbol_table = FirstPass::from_buffer(buf)?;
    f = std::fs::File::open(path)?;
    buf = std::io::BufReader::new(f);
    let iter = io::Reader::new(buf).assembly_lines();
    Ok(SecondPass::new(iter, symbol_table))
}

pub fn assemble_from_slice(
    slice: &[Assembly],
) -> Result<SecondPassTrusted<std::slice::Iter<Assembly>>, hack_interface::Error> {
    let s = FirstPass::from_slice(slice)?;
    Ok(SecondPassTrusted::new(slice.iter(), s))
}

#[cfg(test)]
mod assembly_tests {
    use super::*;

    #[test]
    fn collect_symbol_table() -> Result<(), hack_interface::Error> {
        let rom = b"//Comment\n@0\n(Label)\n//Comment\n@1";
        let symbol_table = FirstPass::from_buffer(&rom[..])?;
        assert_eq!(symbol_table.get("Label"), Some(1.into()));
        Ok(())
    }
}

#[cfg(test)]
mod book_tests {
    use super::*;

    /// Machine code to add 2 and 3 and store result to RAM\[0\].
    pub const TWO_PLUS_THREE: &'static str = "0000000000000010
1110110000010000
0000000000000011
1110000010010000
0000000000000000
1110001100001000
";

    /// Assemble the 2+3 machine code
    #[test]
    pub fn chapter6_assemble_add() -> Result<(), hack_interface::Error> {
        let asm = b"
            @2
            D=A
            @3
            D=D+A
            @0
            M=D
        ";
        let mut machine_code = hack_interface::hack_io::Writer::new(Vec::new());
        for bit16 in crate::assemble_from_bytes(&asm[..])? {
            machine_code.write_instruction(bit16?)?;
        }
        assert_eq!(TWO_PLUS_THREE.as_bytes(), machine_code.as_ref());

        Ok(())
    }

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

    /// Assemble the max machine code (no labels)
    #[test]
    pub fn chapter6_assemble_max_no_label() -> Result<(), hack_interface::Error> {
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

        let mut machine_code = hack_interface::hack_io::Writer::new(Vec::new());
        for bit16 in crate::assemble_from_bytes(&asm[..])? {
            machine_code.write_instruction(bit16?)?;
        }
        assert_eq!(PICK_MAX.as_bytes(), machine_code.as_ref());

        Ok(())
    }

    /// Assemble the max machine code (with labels)
    #[test]
    pub fn chapter6_assemble_max_label() -> Result<(), hack_interface::Error> {
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
        let mut machine_code = hack_interface::hack_io::Writer::new(Vec::new());
        for bit16 in crate::assemble_from_bytes(&asm[..])? {
            machine_code.write_instruction(bit16?)?;
        }
        assert_eq!(PICK_MAX.as_bytes(), machine_code.as_ref());

        Ok(())
    }

    // This was added while I was writing the VM static memory management
    // I wrote a bad test and thought there was an error in how symbols are resolved
    // I didn't see any explicit testing of symbols, so I wrote them and they passed (and I realized VM tests were bad)
    #[test]
    fn test_symbols() {
        let mut a = Assembler::new(SymbolTable::empty());
        let l1 = a
            .pass_line(&Assembly::A(ACommand::Symbol("test.1".to_string())))
            .unwrap();
        assert_eq!(l1, 16.into());
        let l2 = a
            .pass_line(&Assembly::A(ACommand::Symbol("test.2".to_string())))
            .unwrap();
        assert_eq!(l2, 17.into());
        let l3 = a
            .pass_line(&Assembly::A(ACommand::Symbol("test.1".to_string()))) // Same symbol as the first
            .unwrap();
        assert_eq!(l3, 16.into());
    }
}
