//! IO for assembly (.asm) files
//!
//! # FAQ
//!
//! ## Why `i16` for line counting?
//! The [hack_kernel::Computer] and the [ROM][hack_kernel::Rom32K] use a 15 bit address space. Although an .asm file (which is loaded in the ROM) could contain more lines than can be expressed by 15 bits (greater than 32767), the extra lines would not fit into the ROM. By using `i16` and starting from 0 (first bit is always 0), one gets a very convenient representation of a 15 bit address space. [crate::Bit15] contains a check for negative numbers, so will panic if integer overflow happens.
//!
//! ## Why so many `Option`s?
//! `None` represents nothing in the [Reader] buffer. This happens if no lines have been read or if EOF has been reached. It is possible to squint and avoid using `Option`. For example, [Reader::is_empty_line()] could be `false` rather than `None`. The advantage of that squint is that you don't have to deal with `Option` all the time (it is annoying). The disadvantage is that you don't have to deal with EOF explicitly. Even if there was a `is_eof()` function, it would be up to me to remember to check. `Option` forces that check, even if it is only to call `unwrap` (which, for the record, is not done). Explicit is better. The neat thing is that the `Option` design feeds in nicely into the [FirstPass][crate::assembly::FirstPass] and [SecondPass][crate::assembly::SecondPass] iterators.

/// Low level reader of .asm files.
///
/// If you want full control over reading. [crate::assembly::FirstPass] and [crate::assembly::SecondPass] offer simpler abstractions for parsing .asm files.
use hack_interface;

pub struct Reader<R> {
    inner: R,
    buffer: Option<String>,
    pub(super) line: i16,
}

impl<R: std::io::BufRead> Reader<R> {
    /// Reader starts at the first line of the file
    pub fn new(inner: R) -> Self {
        let reader = Self {
            inner,
            buffer: None,
            line: 0,
        };
        reader
    }

    /// Read the next line into the buffer and [cleans][clean_line] it. Returns true if line was read and false if EOF was reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\nlife //carefully";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    /// );
    /// assert_eq!((a, b, c, d), (true, true, false, false));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_line(&mut self) -> Result<bool, hack_interface::Error> {
        let mut temp = "".to_string();
        let read = self.inner.read_line(&mut temp)?;
        if read == 0 {
            self.buffer = None;
            Ok(false)
        } else {
            self.line += 1;
            clean_line(&mut temp);
            self.buffer = Some(temp);
            Ok(true)
        }
    }

    /// Read the next instruction into the buffer, skipping empty lines.
    ///
    /// Returns 0 if EOF was reached, otherwise the number of total lines read across all reads.
    ///
    /// # Examples
    /// ```
    /// let rom = b"I\n\nlike\n//me\nyou";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    /// );
    /// assert_eq!((a, b, c, d), (1, 3, 5, 0));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_instruction(&mut self) -> Result<i16, hack_interface::Error> {
        loop {
            self.read_line()?;
            match self.is_empty_line() {
                None => break Ok(0),
                Some(b) => {
                    if !b {
                        break Ok(self.line);
                    }
                }
            }
        }
    }

    /// Read the next command into the buffer, skipping non-command lines.
    ///
    /// Returns 0 if EOF was reached, otherwise the number of total lines read across all reads.
    ///
    /// # Examples
    /// ```
    /// let rom = b"//Intro\n@1\n(Label)\nM=D";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// let (a, b, c) = (
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    /// );
    /// assert_eq!((a, b, c), (2, 4, 0));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_command(&mut self) -> Result<i16, hack_interface::Error> {
        loop {
            self.read_line()?;
            match self.is_command() {
                None => break Ok(0),
                Some(b) => {
                    if b {
                        break Ok(self.line);
                    }
                }
            }
        }
    }

    /// Is the current line a command (A or C)
    ///
    /// # Examples
    /// ```
    /// let rom = b"@Yes\nYes;\nNo";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(false));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn is_command(&self) -> Option<bool> {
        if let (Some(a), Some(c)) = (self.is_a_command(), self.is_c_command()) {
            Some(a || c)
        } else {
            None
        }
    }

    /// Is the current line an A command (starts with `'@'`)?
    ///
    /// # Examples
    /// ```
    /// let rom = b"@Yes\nNo";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), None);
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn is_a_command(&self) -> Option<bool> {
        match &self.buffer {
            None => None,
            Some(s) => Some(s.starts_with("@")),
        }
    }
    /// Is the current line an C command (contains `'='` or `';'`)?
    ///
    /// # Examples
    /// ```
    /// let rom = b"Yes=\n;Yes\nNo";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), None);
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn is_c_command(&self) -> Option<bool> {
        match &self.buffer {
            None => None,
            Some(s) => Some(s.find(|c| c == ';' || c == '=').is_some()),
        }
    }

    /// Has anything been read into the buffer?
    ///
    /// Will be true before anything has been read or EOF has been reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"@100";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// assert!(reader.is_empty_buffer());
    /// reader.read_line()?;
    /// assert!(!reader.is_empty_buffer());
    /// reader.read_line()?;
    /// assert!(reader.is_empty_buffer());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn is_empty_buffer(&self) -> bool {
        return self.buffer.is_none();
    }

    /// Is the current line empty?
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\n//life //carefully";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(true));
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn is_empty_line(&self) -> Option<bool> {
        match &self.buffer {
            None => None,
            Some(s) => Some(s.len() == 0),
        }
    }

    /// Is the current line a label symbol (starts with `'('`)?
    ///
    /// A label symbol is bound to the instruction memory location holding the next command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"(Yes\nNo";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), None);
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn is_label(&self) -> Option<bool> {
        match &self.buffer {
            None => None,
            Some(s) => Some(s.starts_with("(")),
        }
    }

    /// Parses the label on the current line.
    ///
    /// A label does not start with a number, only includes alphanumeric, `_`, `.`, `$`, and `:` characters.
    /// A label cannot be a reserved symbol.
    ///
    /// This assumes the current line is a label.
    ///
    /// # Examples
    /// ```
    /// let rom = b"(Yes)";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_label()?, "Yes".to_string());
    /// reader.read_line()?;
    /// assert!(reader.parse_label().is_err());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn parse_label(&self) -> Result<String, hack_interface::Error> {
        if let Some(a) = &self.buffer {
            let s = a
                .get(1..a.len() - 1)
                .ok_or(hack_interface::Error::AssemblyLabel(self.line))?;
            if s.chars()
                .nth(0)
                .ok_or(hack_interface::Error::AssemblyLabel(self.line))?
                .is_numeric()
            {
                Err(hack_interface::Error::AssemblyLabel(self.line))
            } else if !s
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == '$' || c == ':')
            {
                Err(hack_interface::Error::AssemblyLabel(self.line))
            } else {
                Ok(s.to_string())
            }
        } else {
            Err(hack_interface::Error::AssemblyLabel(self.line))
        }
    }

    /// Parse an A-command.
    ///
    /// This assumes the current line is an A-command.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::assembly_io::ACommand;
    /// let rom = b"@100\n@Symbol\n@SP";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_a_command()?,
    ///     ACommand::Address(100)
    /// );
    ///
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_a_command()?,
    ///     ACommand::Symbol("Symbol".to_string())
    /// );
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_a_command()?,
    ///     ACommand::Reserved(hack_assembler::ReservedSymbols::SP)
    /// );
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn parse_a_command(&self) -> Result<ACommand, hack_interface::Error> {
        use std::convert::TryInto;
        let line = self.line;
        let a = self
            .buffer
            .as_ref()
            .ok_or(hack_interface::Error::ACommand(line))?;
        let first = a
            .chars()
            .next()
            .ok_or(hack_interface::Error::ACommand(line))?;
        if first != '@' {
            Err(hack_interface::Error::ACommand(line))
        } else {
            let s = a.get(1..).ok_or(hack_interface::Error::ACommand(line))?;
            match s.parse::<i16>() {
                Ok(i) => Ok(ACommand::Address(i)),
                Err(_) => {
                    match s.try_into() {
                        Ok(r) => Ok(ACommand::Reserved(r)),
                        Err(_) => {
                            // Validation happens at label parsing
                            // Invalid A command symbols are allowed, as they can't reference labels
                            Ok(ACommand::Symbol(s.to_string()))
                        }
                    }
                }
            }
        }
    }

    /// Parse an C-command.
    ///
    /// This assumes the current line is an C-command.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::assembly_io::{CCommand, CDest, CComp, CJump};
    /// let rom = b"M=D+A;JGE";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_c_command()?,
    ///     CCommand::new(CDest::M, CComp::DPlusA, CJump::GreaterEqual)
    /// );
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    ///
    pub fn parse_c_command(&self) -> Result<CCommand, hack_interface::Error> {
        let line = self.line;
        let str_command = self
            .buffer
            .as_ref()
            .ok_or(hack_interface::Error::CCommand(line))?;

        match str_command.parse() {
            Ok(c) => Ok(c),
            Err(()) => Err(hack_interface::Error::CCommand(line)),
        }
    }

    /// An iterator over assembly instruction.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::assembly_io::{ACommand, CCommand, CDest, CComp, CJump, AssemblyLine};
    /// let rom = b"(Now)\n//Comment\n@100\nM=D+A;JGE";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// let mut lines = reader.assembly_lines();
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     AssemblyLine::Label("Now".to_string())
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     AssemblyLine::Empty
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     AssemblyLine::A(ACommand::Address(100))
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     AssemblyLine::C(CCommand::new(CDest::M, CComp::DPlusA, CJump::GreaterEqual))
    /// );
    /// assert!(lines.next().is_none());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn assembly_lines(self) -> AssemblyLines<R> {
        AssemblyLines { inner: self }
    }

    /// An iterator for the first pass.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::assembly_io::FirstPassLine;
    /// let rom = b"//Comment\n(Now)\n@100";
    /// let mut reader = hack_assembler::assembly_io::Reader::new(&rom[..]);
    /// let mut first_pass = reader.first_pass();
    /// assert_eq!(
    ///     first_pass.next().unwrap().unwrap(),
    ///     FirstPassLine::Empty
    /// );
    /// assert_eq!(
    ///     first_pass.next().unwrap().unwrap(),
    ///     FirstPassLine::Label("Now".to_string())
    /// );
    /// assert_eq!(
    ///     first_pass.next().unwrap().unwrap(),
    ///     FirstPassLine::Command
    /// );
    /// assert!(first_pass.next().is_none());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn first_pass(&mut self) -> FirstPassLines<R> {
        FirstPassLines { inner: self }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub enum AssemblyLine {
    Empty,
    A(ACommand),
    C(CCommand),
    Label(String),
}

/// An iterator over assembly lines. Create with [Reader::assembly_lines()].
pub struct AssemblyLines<R> {
    inner: Reader<R>,
}

impl<R: std::io::BufRead> std::iter::Iterator for AssemblyLines<R> {
    type Item = Result<AssemblyLine, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.read_line() {
            Ok(false) => return None,
            Ok(true) => {}
            Err(e) => return Some(Err(e)),
        };
        if self.inner.is_empty_line().unwrap() {
            Some(Ok(AssemblyLine::Empty))
        } else if self.inner.is_label().unwrap() {
            let label = match self.inner.parse_label() {
                Ok(s) => s,
                Err(e) => return Some(Err(e)),
            };
            Some(Ok(AssemblyLine::Label(label)))
        } else if self.inner.is_a_command().unwrap() {
            match self.inner.parse_a_command() {
                Ok(a) => Some(Ok(AssemblyLine::A(a))),
                Err(e) => Some(Err(e)),
            }
        } else if self.inner.is_c_command().unwrap() {
            match self.inner.parse_c_command() {
                Ok(c) => Some(Ok(AssemblyLine::C(c))),
                Err(e) => Some(Err(e)),
            }
        } else {
            Some(Err(hack_interface::Error::Unknown(self.inner.line)))
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FirstPassLine {
    Empty,
    Command,
    Label(String),
}

///First pass iterator returning [FirstPassLine].
///
/// It returns an item for each line, allowing one to count the input lines from the BufRead.
pub struct FirstPassLines<'a, R> {
    inner: &'a mut Reader<R>,
}

impl<'a, R: std::io::BufRead> std::iter::Iterator for FirstPassLines<'a, R> {
    type Item = Result<FirstPassLine, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.read_line() {
            Ok(false) => return None,
            Ok(true) => {}
            Err(e) => return Some(Err(e)),
        };

        if self.inner.is_empty_line().unwrap() {
            Some(Ok(FirstPassLine::Empty))
        } else if self.inner.is_label().unwrap() {
            let label = match self.inner.parse_label() {
                Ok(s) => s,
                Err(e) => return Some(Err(e)),
            };
            Some(Ok(FirstPassLine::Label(label)))
        } else if self.inner.is_command().unwrap() {
            Some(Ok(FirstPassLine::Command))
        } else {
            Some(Err(hack_interface::Error::Unknown(self.inner.line)))
        }
    }
}

/// Remove all white space and comment characters. May leave an empty string.
///
/// Comment characters are those following `"//"` (including itself).
///
/// # Examples
/// ```
/// use hack_assembler::assembly_io::clean_line;
/// let mut s = "in st //spaces and trailing comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "inst".to_string());
/// clean_line(&mut s);
/// assert_eq!(s, "inst".to_string());
/// s = "// Starting comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "".to_string());
/// ```
pub fn clean_line(line: &mut String) {
    line.retain(|c| !c.is_whitespace());
    let no_comments = match line.split_once("//") {
        None => line.to_string(),
        Some((instruction, _)) => instruction.to_string(),
    };
    line.clear();
    line.push_str(&no_comments);
}

/// A parsed A-command can be either an address, a reserved symbol, or a user defined symbol
#[derive(Debug, PartialEq, Eq)]
pub enum ACommand {
    Address(i16),
    Reserved(crate::ReservedSymbols),
    Symbol(String),
}

#[derive(Debug, PartialEq, Eq)]
pub struct CCommand {
    dest: CDest,
    comp: CComp,
    jump: CJump,
}

impl CCommand {
    pub fn new(dest: CDest, comp: CComp, jump: CJump) -> Self {
        CCommand { dest, comp, jump }
    }

    pub fn new_dest(dest: CDest, comp: CComp) -> Self {
        CCommand {
            dest,
            comp,
            jump: CJump::Null,
        }
    }

    pub fn new_jump(comp: CComp, jump: CJump) -> Self {
        CCommand {
            dest: CDest::Null,
            comp,
            jump,
        }
    }
}

impl std::str::FromStr for CCommand {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (destination_str, rest) = match s.split_once("=") {
            Some((d, r)) => (Some(d), r),
            None => (None, s),
        };

        let dest = match destination_str {
            Some(d) => d.parse()?,
            None => CDest::Null,
        };

        let (command_str, jump_str) = match rest.split_once(";") {
            Some((c, j)) => (c, Some(j)),
            None => (rest, None),
        };

        let comp = command_str.parse()?;

        let jump = match jump_str {
            Some(j) => j.parse()?,
            None => CJump::Null,
        };

        Ok(CCommand { dest, comp, jump })
    }
}

impl std::convert::From<CCommand> for hack_interface::Bit16 {
    fn from(value: CCommand) -> Self {
        let dest = <[bool; 3]>::from(value.dest);
        let comp = <[bool; 7]>::from(value.comp);
        let jump = <[bool; 3]>::from(value.jump);

        hack_interface::Bit16::from([
            true, true, true, comp[0], comp[1], comp[2], comp[3], comp[4], comp[5], comp[6],
            dest[0], dest[1], dest[2], jump[0], jump[1], jump[2],
        ])
    }
}

impl std::fmt::Display for CCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let dest_sep = match self.dest {
            CDest::Null => "",
            _ => "=",
        };
        let jump_sep = match self.jump {
            CJump::Null => "",
            _ => ";",
        };
        write!(
            f,
            "{}{dest_sep}{}{jump_sep}{}",
            self.dest, self.comp, self.jump
        )
    }
}

/// The comp part of the C instruction
#[derive(Debug, PartialEq, Eq)]
pub enum CComp {
    Zero,
    One,
    MinumOne,
    D,
    A,
    NotD,
    NotA,
    MinusD,
    MinusA,
    DPlusOne,
    APlusOne,
    DMinusOne,
    AMinusOne,
    DPlusA,
    DMinusA,
    AMinusD,
    DAndA,
    DOrA,
    M,
    NotM,
    MinusM,
    MPlusOne,
    MMinusOne,
    DPlusM,
    DMinusM,
    MMinusD,
    DAndM,
    DOrM,
}

impl CComp {
    /// The first bit of the comp instruction. Is A register a value or a memory address?
    fn a_m_flag(self) -> bool {
        match self {
            CComp::Zero => false,
            CComp::One => false,
            CComp::MinumOne => false,
            CComp::D => false,
            CComp::A => false,
            CComp::NotD => false,
            CComp::NotA => false,
            CComp::MinusD => false,
            CComp::MinusA => false,
            CComp::DPlusOne => false,
            CComp::APlusOne => false,
            CComp::DMinusOne => false,
            CComp::AMinusOne => false,
            CComp::DPlusA => false,
            CComp::DMinusA => false,
            CComp::AMinusD => false,
            CComp::DAndA => false,
            CComp::DOrA => false,
            CComp::M => true,
            CComp::NotM => true,
            CComp::MinusM => true,
            CComp::MPlusOne => true,
            CComp::MMinusOne => true,
            CComp::DPlusM => true,
            CComp::DMinusM => true,
            CComp::MMinusD => true,
            CComp::DAndM => true,
            CComp::DOrM => true,
        }
    }
}

impl std::str::FromStr for CComp {
    type Err = (); // Informative error message happens during parsing

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "0" => Ok(Self::Zero),
            "1" => Ok(Self::One),
            "-1" => Ok(Self::MinumOne),
            "D" => Ok(Self::D),
            "A" => Ok(Self::A),
            "!D" => Ok(Self::NotD),
            "!A" => Ok(Self::NotA),
            "-D" => Ok(Self::MinusD),
            "-A" => Ok(Self::MinusA),
            "D+1" => Ok(Self::DPlusOne),
            "A+1" => Ok(Self::APlusOne),
            "D-1" => Ok(Self::DMinusOne),
            "A-1" => Ok(Self::AMinusOne),
            "D+A" => Ok(Self::DPlusA),
            "D-A" => Ok(Self::DMinusA),
            "A-D" => Ok(Self::AMinusD),
            "D&A" => Ok(Self::DAndA),
            "D|A" => Ok(Self::DOrA),
            "M" => Ok(Self::M),
            "!M" => Ok(Self::NotM),
            "-M" => Ok(Self::MinusM),
            "M+1" => Ok(Self::MPlusOne),
            "M-1" => Ok(Self::MMinusOne),
            "D+M" => Ok(Self::DPlusM),
            "D-M" => Ok(Self::DMinusM),
            "M-D" => Ok(Self::MMinusD),
            "D&M" => Ok(Self::DAndM),
            "D|M" => Ok(Self::DOrM),
            _ => Err(()),
        }
    }
}

impl std::convert::From<CComp> for [bool; 7] {
    fn from(value: CComp) -> Self {
        let c = match value {
            CComp::Zero => hack_kernel::arithmetic::ALU_ZERO,
            CComp::One => hack_kernel::arithmetic::ALU_ONE,
            CComp::MinumOne => hack_kernel::arithmetic::ALU_MINUS_ONE,
            CComp::D => hack_kernel::arithmetic::ALU_X,
            CComp::A | CComp::M => hack_kernel::arithmetic::ALU_Y,
            CComp::NotD => hack_kernel::arithmetic::ALU_X_NOT,
            CComp::NotA | CComp::NotM => hack_kernel::arithmetic::ALU_Y_NOT,
            CComp::MinusD => hack_kernel::arithmetic::ALU_X_MINUS,
            CComp::MinusA | CComp::MinusM => hack_kernel::arithmetic::ALU_Y_MINUS,
            CComp::DPlusOne => hack_kernel::arithmetic::ALU_X_PLUS1,
            CComp::APlusOne | CComp::MPlusOne => hack_kernel::arithmetic::ALU_Y_PLUS1,
            CComp::DMinusOne => hack_kernel::arithmetic::ALU_X_MINUS1,
            CComp::AMinusOne | CComp::MMinusOne => hack_kernel::arithmetic::ALU_Y_MINUS1,
            CComp::DPlusA | CComp::DPlusM => hack_kernel::arithmetic::ALU_X_PLUS_Y,
            CComp::DMinusA | CComp::DMinusM => hack_kernel::arithmetic::ALU_X_MINUS_Y,
            CComp::AMinusD | CComp::MMinusD => hack_kernel::arithmetic::ALU_Y_MINUS_X,
            CComp::DAndA | CComp::DAndM => hack_kernel::arithmetic::ALU_X_AND_Y,
            CComp::DOrA | CComp::DOrM => hack_kernel::arithmetic::ALU_X_OR_Y,
        };

        [value.a_m_flag(), c[0], c[1], c[2], c[3], c[4], c[5]]
    }
}

impl std::fmt::Display for CComp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::MinumOne => "-1",
            Self::D => "D",
            Self::A => "A",
            Self::NotD => "!D",
            Self::NotA => "!A",
            Self::MinusD => "-D",
            Self::MinusA => "-A",
            Self::DPlusOne => "D+1",
            Self::APlusOne => "A+1",
            Self::DMinusOne => "D-1",
            Self::AMinusOne => "A-1",
            Self::DPlusA => "D+A",
            Self::DMinusA => "D-A",
            Self::AMinusD => "A-D",
            Self::DAndA => "D&A",
            Self::DOrA => "D|A",
            Self::M => "M",
            Self::NotM => "!M",
            Self::MinusM => "-M",
            Self::MPlusOne => "M+1",
            Self::MMinusOne => "M-1",
            Self::DPlusM => "D+M",
            Self::DMinusM => "D-M",
            Self::MMinusD => "M-D",
            Self::DAndM => "D&M",
            Self::DOrM => "D|M",
        };
        write!(f, "{}", s)
    }
}

/// The destination part of the C command
#[derive(Debug, PartialEq, Eq)]
pub enum CDest {
    Null,
    M,
    D,
    MD,
    A,
    AM,
    AD,
    AMD,
}

impl std::str::FromStr for CDest {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(CDest::Null),
            "M" => Ok(CDest::M),
            "D" => Ok(CDest::D),
            "MD" => Ok(CDest::MD),
            "A" => Ok(CDest::A),
            "AM" => Ok(CDest::AM),
            "AD" => Ok(CDest::AD),
            "AMD" => Ok(CDest::AMD),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for CDest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CDest::Null => "",
            CDest::M => "M",
            CDest::D => "D",
            CDest::MD => "MD",
            CDest::A => "A",
            CDest::AM => "AM",
            CDest::AD => "AD",
            CDest::AMD => "AMD",
        };
        write!(f, "{}", s)
    }
}

impl std::convert::From<CDest> for [bool; 3] {
    fn from(value: CDest) -> Self {
        match value {
            CDest::Null => [false, false, false],
            CDest::M => [false, false, true],
            CDest::D => [false, true, false],
            CDest::MD => [false, true, true],
            CDest::A => [true, false, false],
            CDest::AM => [true, false, true],
            CDest::AD => [true, true, false],
            CDest::AMD => [true, true, true],
        }
    }
}

/// The jump part of the C command
#[derive(Debug, PartialEq, Eq)]
pub enum CJump {
    Null,
    Greater,
    Equal,
    GreaterEqual,
    Less,
    NotEqual,
    LessEqual,
    Jump,
}

impl std::str::FromStr for CJump {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(CJump::Null),
            "JGT" => Ok(CJump::Greater),
            "JEQ" => Ok(CJump::Equal),
            "JGE" => Ok(CJump::GreaterEqual),
            "JLT" => Ok(CJump::Less),
            "JNE" => Ok(CJump::NotEqual),
            "JLE" => Ok(CJump::LessEqual),
            "JMP" => Ok(CJump::Jump),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for CJump {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CJump::Null => "",
            CJump::Greater => "JGT",
            CJump::Equal => "JEQ",
            CJump::GreaterEqual => "JGE",
            CJump::Less => "JLT",
            CJump::NotEqual => "JNE",
            CJump::LessEqual => "JLE",
            CJump::Jump => "JMP",
        };
        write!(f, "{}", s)
    }
}

impl std::convert::From<CJump> for [bool; 3] {
    fn from(value: CJump) -> Self {
        match value {
            CJump::Null => [false, false, false],
            CJump::Greater => [false, false, true],
            CJump::Equal => [false, true, false],
            CJump::GreaterEqual => [false, true, true],
            CJump::Less => [true, false, false],
            CJump::NotEqual => [true, false, true],
            CJump::LessEqual => [true, true, false],
            CJump::Jump => [true, true, true],
        }
    }
}

#[cfg(test)]
mod assembly_io_tests {
    use super::*;
    #[test]
    fn test_parse_c_command() -> Result<(), hack_interface::Error> {
        let rom = b"!A;JMP\nD=M-D";
        let mut reader = Reader::new(&rom[..]);
        reader.read_line()?;
        let mut c = reader.parse_c_command()?;
        assert_eq!(
            c,
            CCommand {
                dest: CDest::Null,
                comp: CComp::NotA,
                jump: CJump::Jump
            }
        );
        assert_eq!(hack_interface::Bit16::from(c), "1110110001000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(
            c,
            CCommand {
                dest: CDest::D,
                comp: CComp::MMinusD,
                jump: CJump::Null
            }
        );
        assert_eq!(hack_interface::Bit16::from(c), "1111000111010000".parse()?);
        Ok(())
    }

    #[test]
    /// 0 if calculation refers to A register, 1 if calculation refers to value of M
    fn test_c_command_flag() -> Result<(), hack_interface::Error> {
        let rom = b"0;JMP\nA;JMP\nM;JMP";
        let mut reader = crate::assembly_io::Reader::new(&rom[..]);
        reader.read_line()?;
        let mut c = reader.parse_c_command()?;
        assert_eq!(
            c,
            CCommand {
                dest: CDest::Null,
                comp: CComp::Zero,
                jump: CJump::Jump
            }
        );
        assert_eq!(hack_interface::Bit16::from(c), "1110101010000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(
            c,
            CCommand {
                dest: CDest::Null,
                comp: CComp::A,
                jump: CJump::Jump
            }
        );
        assert_eq!(hack_interface::Bit16::from(c), "1110110000000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(
            c,
            CCommand {
                dest: CDest::Null,
                comp: CComp::M,
                jump: CJump::Jump
            }
        );
        assert_eq!(hack_interface::Bit16::from(c), "1111110000000111".parse()?);
        Ok(())
    }
}
