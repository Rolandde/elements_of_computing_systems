//! Assembler that converts from `.asm` assembly format to `.hack` machine instructions format.
//!
//! You probably want to use [assemble_from_bytes] or [assemble_from_file].
//!
//! As labels can be used before they are defined, a [FirstPass] is necessary to build the symbol table. Note that the danger is that everything will work just fine with a [SecondPass] even if labels are present in your assembly code. This will result in wrong machine code, as an A-command with a label (`@END`) will be misinterpreted as a new address in RAM rather than an instruction position in the ROM. There are ways (that either increase code complexity or decrease efficiency) to prevent this type of bug, but the current solution is to always run first pass, unless you know it is not needed.

pub mod assembly_io;

/// An iterator over the assembly labels and the commands they point to.
///
/// Used to create the [SymbolTable] needed for the [SecondPass]
pub struct FirstPass<R> {
    inner: crate::assembly_io::Reader<R>,
    command_count: i16,
}

impl<R: std::io::BufRead> FirstPass<R> {
    /// Creates the iterator
    pub fn new(buffer: R) -> Self {
        Self {
            inner: crate::assembly_io::Reader::new(buffer),
            command_count: 0,
        }
    }

    /// Generate the [SymbolTable] directly.
    ///
    /// # Examples
    /// ```
    /// let rom = b"//Comment\n(Label)\n//Comment\n@1";
    /// let symbol_table = hack_assembler::FirstPass::new_symbol_table(&rom[..])?;
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn new_symbol_table(buffer: R) -> Result<SymbolTable, hack_interface::Error> {
        let iter = Self::new(buffer);
        let mut st = SymbolTable::new();

        for label in iter {
            let LabelAddress {
                label,
                command_count,
                label_line,
            } = label?;
            // Duplicated keys are not allowed
            if st.inner.contains_key(&label) {
                Err(hack_interface::Error::SymbolTable(label_line))?
            }
            // Commands start at 0
            st.inner.insert(label, (command_count - 1).into());
        }

        Ok(st)
    }

    /// Read the next instruction.
    ///
    /// Returns the total number of lines read so far. 0 if EOF has been reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"//Nothing\n@Yes\nNo";
    /// let mut reader = hack_assembler::FirstPass::new(&rom[..]);
    /// assert_eq!(reader.read_instruction()?, 2);
    /// assert_eq!(reader.read_instruction()?, 3);
    /// assert_eq!(reader.read_instruction()?, 0);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_instruction(&mut self) -> Result<i16, hack_interface::Error> {
        let lines_read = self.inner.read_instruction()?;
        match self.inner.is_command() {
            Some(true) => self.command_count += 1,
            _ => {}
        }
        Ok(lines_read)
    }

    /// Get label and its associated address.
    ///
    /// This assumes the reader is at a label.
    ///
    /// # Examples
    /// ```
    /// let rom = b"//Comment\n(Label)\n//Comment\n@1";
    /// let mut first_pass = hack_assembler::FirstPass::new(&rom[..]);
    /// first_pass.read_instruction()?;
    /// assert_eq!(
    ///     first_pass.get_label_address()?,
    ///     hack_assembler::LabelAddress{
    ///         label: "Label".to_string(),
    ///         command_count: 1,
    ///         label_line: 2,
    ///     }
    /// );
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn get_label_address(&mut self) -> Result<LabelAddress, hack_interface::Error> {
        let label_line = self.inner.line;
        let label = self
            .inner
            .parse_label()?
            .ok_or(hack_interface::Error::AssemblyLabel(label_line))?;
        self.read_instruction()?;

        match self.inner.is_command() {
            Some(true) => Ok(LabelAddress {
                label,
                command_count: self.command_count,
                label_line,
            }),
            // Command does not follow a label
            Some(false) => Err(hack_interface::Error::AssemblyLabel(label_line)),
            // End of file following label
            None => Err(hack_interface::Error::AssemblyLabel(label_line)),
        }
    }
}

impl<R: std::io::BufRead> std::iter::Iterator for FirstPass<R> {
    type Item = Result<LabelAddress, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.read_instruction() {
                Ok(_) => {}
                Err(e) => break Some(Err(e)),
            }
            match self.inner.is_label() {
                None => break None,
                Some(true) => break Some(self.get_label_address()),
                Some(false) => continue,
            }
        }
    }
}

/// An iterator that spits out the binary .hack format.
///
/// [SymbolTable] can be populated by [FirstPass] if labels are in the assembly file.
pub struct SecondPass<R> {
    inner: crate::assembly_io::Reader<R>,
    symbol_table: SymbolTable,
    variable_symbol_count: i16,
}

impl<R: std::io::BufRead> SecondPass<R> {
    pub fn new(buffer: R, symbol_table: SymbolTable) -> Self {
        Self {
            inner: crate::assembly_io::Reader::new(buffer),
            symbol_table,
            variable_symbol_count: 16,
        }
    }

    /// Read to the next command, return true if C-command and false if A-command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"//Comment\n@h\nA;JMP";
    /// let mut second_pass = hack_assembler::SecondPass::new(
    ///     &rom[..],
    ///     hack_assembler::SymbolTable::new(),
    /// );
    /// assert_eq!(second_pass.read_command()?, Some(false));
    /// assert_eq!(second_pass.read_command()?, Some(true));
    /// assert_eq!(second_pass.read_command()?, None);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_command(&mut self) -> Result<Option<bool>, hack_interface::Error> {
        self.inner.read_command()?;

        match self.inner.is_c_command() {
            Some(b) => Ok(Some(b)),
            None => Ok(None),
        }
    }

    /// Parses an A-command, resolving symbols if necessary.
    ///
    /// Assumes the current line is an A-command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"@h\n@R6\n@3\n@h\n@h2";
    /// let mut second_pass = hack_assembler::SecondPass::new(
    ///     &rom[..],
    ///     hack_assembler::SymbolTable::new(),
    /// );
    /// second_pass.read_command()?;
    /// assert_eq!(second_pass.parse_a_command()?, 16.into()); // Custom address starts at 16
    /// second_pass.read_command()?;
    /// assert_eq!(second_pass.parse_a_command()?, 6.into());  // Predefined constant address
    /// second_pass.read_command()?;
    /// assert_eq!(second_pass.parse_a_command()?, 3.into());
    /// second_pass.read_command()?;
    /// assert_eq!(second_pass.parse_a_command()?, 16.into());
    /// second_pass.read_command()?;
    /// assert_eq!(second_pass.parse_a_command()?, 17.into());
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn parse_a_command(&mut self) -> Result<hack_interface::Bit16, hack_interface::Error> {
        match self.inner.parse_a_command()? {
            crate::assembly_io::ACommand::Address(b) => Ok(b.into()),
            crate::assembly_io::ACommand::Reserved(r) => Ok(hack_interface::Bit15::from(r).into()),
            crate::assembly_io::ACommand::Symbol(s) => match self.symbol_table.inner.get(&s) {
                Some(b) => Ok(hack_interface::Bit16::from(*b)),
                None => {
                    let current_address = self.variable_symbol_count.into();
                    self.symbol_table.inner.insert(s, current_address);
                    self.variable_symbol_count += 1;
                    Ok(current_address.into())
                }
            },
        }
    }
}

impl<R: std::io::BufRead> std::iter::Iterator for SecondPass<R> {
    type Item = Result<hack_interface::Bit16, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let c_command = match self.read_command() {
                Ok(Some(c)) => c,
                Ok(None) => break None,
                Err(e) => break Some(Err(e)),
            };

            if c_command {
                break Some(
                    self.inner
                        .parse_c_command()
                        .map(|ok| hack_interface::Bit16::from(ok)),
                );
            } else {
                break Some(self.parse_a_command());
            }
        }
    }
}

/// Symbol table generated by the first pass through the assembly code.
///
/// Created by [FirstPass]. If you are certain the assembly code does not use any custom symbols, this can be used directly with [SecondPass].
pub struct SymbolTable {
    inner: std::collections::HashMap<String, hack_interface::Bit15>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            inner: std::collections::HashMap::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ReservedSymbols {
    SP,
    LCL,
    ARG,
    THIS,
    THAT,
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    SCREEN,
    KBD,
}

impl ReservedSymbols {
    pub fn is_reserved(symbol: &str) -> bool {
        use std::convert::TryFrom;
        match Self::try_from(symbol) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
}

impl std::convert::TryFrom<&str> for ReservedSymbols {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "SP" => Ok(ReservedSymbols::SP),
            "LCL" => Ok(ReservedSymbols::LCL),
            "ARG" => Ok(ReservedSymbols::ARG),
            "THIS" => Ok(ReservedSymbols::THIS),
            "THAT" => Ok(ReservedSymbols::THAT),
            "R0" => Ok(ReservedSymbols::R0),
            "R1" => Ok(ReservedSymbols::R1),
            "R2" => Ok(ReservedSymbols::R2),
            "R3" => Ok(ReservedSymbols::R3),
            "R4" => Ok(ReservedSymbols::R4),
            "R5" => Ok(ReservedSymbols::R5),
            "R6" => Ok(ReservedSymbols::R6),
            "R7" => Ok(ReservedSymbols::R7),
            "R8" => Ok(ReservedSymbols::R8),
            "R9" => Ok(ReservedSymbols::R9),
            "R10" => Ok(ReservedSymbols::R10),
            "R11" => Ok(ReservedSymbols::R11),
            "R12" => Ok(ReservedSymbols::R12),
            "R13" => Ok(ReservedSymbols::R13),
            "R14" => Ok(ReservedSymbols::R14),
            "R15" => Ok(ReservedSymbols::R15),
            "SCREEN" => Ok(ReservedSymbols::SCREEN),
            "KBD" => Ok(ReservedSymbols::KBD),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for ReservedSymbols {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ReservedSymbols::SP => "SP",
            ReservedSymbols::LCL => "LCL",
            ReservedSymbols::ARG => "ARG",
            ReservedSymbols::THIS => "THIS",
            ReservedSymbols::THAT => "THAT",
            ReservedSymbols::R0 => "R0",
            ReservedSymbols::R1 => "R1",
            ReservedSymbols::R2 => "R2",
            ReservedSymbols::R3 => "R3",
            ReservedSymbols::R4 => "R4",
            ReservedSymbols::R5 => "R5",
            ReservedSymbols::R6 => "R6",
            ReservedSymbols::R7 => "R7",
            ReservedSymbols::R8 => "R8",
            ReservedSymbols::R9 => "R9",
            ReservedSymbols::R10 => "R10",
            ReservedSymbols::R11 => "R11",
            ReservedSymbols::R12 => "R12",
            ReservedSymbols::R13 => "R13",
            ReservedSymbols::R14 => "R14",
            ReservedSymbols::R15 => "R15",
            ReservedSymbols::SCREEN => "SCREEN",
            ReservedSymbols::KBD => "KBD",
        };

        write!(f, "{}", s)
    }
}

impl std::convert::From<ReservedSymbols> for hack_interface::Bit15 {
    fn from(value: ReservedSymbols) -> Self {
        match value {
            ReservedSymbols::SP => 0.into(),
            ReservedSymbols::LCL => 1.into(),
            ReservedSymbols::ARG => 2.into(),
            ReservedSymbols::THIS => 3.into(),
            ReservedSymbols::THAT => 4.into(),
            ReservedSymbols::R0 => 0.into(),
            ReservedSymbols::R1 => 1.into(),
            ReservedSymbols::R2 => 2.into(),
            ReservedSymbols::R3 => 3.into(),
            ReservedSymbols::R4 => 4.into(),
            ReservedSymbols::R5 => 5.into(),
            ReservedSymbols::R6 => 6.into(),
            ReservedSymbols::R7 => 7.into(),
            ReservedSymbols::R8 => 8.into(),
            ReservedSymbols::R9 => 9.into(),
            ReservedSymbols::R10 => 10.into(),
            ReservedSymbols::R11 => 11.into(),
            ReservedSymbols::R12 => 12.into(),
            ReservedSymbols::R13 => 13.into(),
            ReservedSymbols::R14 => 14.into(),
            ReservedSymbols::R15 => 15.into(),
            ReservedSymbols::SCREEN => 16385.into(),
            ReservedSymbols::KBD => 24576.into(),
        }
    }
}

impl std::convert::From<ReservedSymbols> for hack_interface::Bit16 {
    fn from(value: ReservedSymbols) -> Self {
        hack_interface::Bit15::from(value).into()
    }
}

/// The assembly you get after the second pass, with all symbols removed.
pub enum CleanAssembly {
    A(hack_interface::Bit15),
    C(CCommand),
}

impl std::convert::From<ReservedSymbols> for CleanAssembly {
    fn from(value: ReservedSymbols) -> Self {
        match value {
            ReservedSymbols::SP => Self::A(ReservedSymbols::SP.into()),
            ReservedSymbols::LCL => Self::A(ReservedSymbols::LCL.into()),
            ReservedSymbols::ARG => Self::A(ReservedSymbols::ARG.into()),
            ReservedSymbols::THIS => Self::A(ReservedSymbols::THIS.into()),
            ReservedSymbols::THAT => Self::A(ReservedSymbols::THAT.into()),
            ReservedSymbols::R0 => Self::A(ReservedSymbols::R0.into()),
            ReservedSymbols::R1 => Self::A(ReservedSymbols::R1.into()),
            ReservedSymbols::R2 => Self::A(ReservedSymbols::R2.into()),
            ReservedSymbols::R3 => Self::A(ReservedSymbols::R3.into()),
            ReservedSymbols::R4 => Self::A(ReservedSymbols::R4.into()),
            ReservedSymbols::R5 => Self::A(ReservedSymbols::R5.into()),
            ReservedSymbols::R6 => Self::A(ReservedSymbols::R6.into()),
            ReservedSymbols::R7 => Self::A(ReservedSymbols::R7.into()),
            ReservedSymbols::R8 => Self::A(ReservedSymbols::R8.into()),
            ReservedSymbols::R9 => Self::A(ReservedSymbols::R9.into()),
            ReservedSymbols::R10 => Self::A(ReservedSymbols::R10.into()),
            ReservedSymbols::R11 => Self::A(ReservedSymbols::R11.into()),
            ReservedSymbols::R12 => Self::A(ReservedSymbols::R12.into()),
            ReservedSymbols::R13 => Self::A(ReservedSymbols::R13.into()),
            ReservedSymbols::R14 => Self::A(ReservedSymbols::R14.into()),
            ReservedSymbols::R15 => Self::A(ReservedSymbols::R15.into()),
            ReservedSymbols::SCREEN => Self::A(ReservedSymbols::SCREEN.into()),
            ReservedSymbols::KBD => Self::A(ReservedSymbols::KBD.into()),
        }
    }
}

impl std::convert::From<CCommand> for CleanAssembly {
    fn from(value: CCommand) -> Self {
        Self::C(value)
    }
}

impl std::convert::From<CleanAssembly> for hack_interface::Bit16 {
    fn from(value: CleanAssembly) -> Self {
        match value {
            CleanAssembly::A(a) => a.into(),
            CleanAssembly::C(c) => c.into(),
        }
    }
}

/// Convenience container for a label that has been read
#[derive(Debug, PartialEq, Eq)]
pub struct LabelAddress {
    /// The label
    pub label: String,
    /// Counting only commands, which command line does the label refer to?
    pub command_count: i16,
    /// Total raw lines read to get to the label
    pub label_line: i16,
}

/// Two pass assembly from a byte source.
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
pub fn assemble_from_bytes(from: &[u8]) -> Result<SecondPass<&[u8]>, hack_interface::Error> {
    let symbol_table = FirstPass::new_symbol_table(from)?;
    Ok(SecondPass::new(from, symbol_table))
}

/// Two pass assembly from a `.asm` file.
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
) -> Result<SecondPass<std::io::BufReader<std::fs::File>>, hack_interface::Error> {
    let mut f = std::fs::File::open(path.as_ref())?;
    let mut buf = std::io::BufReader::new(f);
    let symbol_table = FirstPass::new_symbol_table(buf)?;
    f = std::fs::File::open(path)?;
    buf = std::io::BufReader::new(f);
    Ok(SecondPass::new(buf, symbol_table))
}

pub use assembly_io::{ACommand, CCommand, CComp, CDest, CJump};

#[cfg(test)]
mod assembly_tests {
    use super::*;

    #[test]
    fn collect_symbol_table() -> Result<(), hack_interface::Error> {
        let rom = b"//Comment\n@0\n(Label)\n//Comment\n@1";
        let symbol_table = FirstPass::new_symbol_table(&rom[..])?;
        assert_eq!(symbol_table.inner.get("Label"), Some(&1.into()));
        Ok(())
    }
}

#[cfg(test)]
mod book_tests {

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
}
