//! IO for assembly (.asm) files
//!
//! # FAQ
//!
//! ## Why `i16` for line counting?
//! The [hack_kernel::Computer] and the [ROM][hack_kernel::Rom32K] use a 15 bit address space. Although an .asm file (which is loaded in the ROM) could contain more lines than can be expressed by 15 bits (greater than 32767), the extra lines would not fit into the ROM. By using `i16` and starting from 0 (first bit is always 0), one gets a very convenient representation of a 15 bit address space. [hack_interface::Bit15] contains a check for negative numbers, so will panic if integer overflow happens.
//!
//! ## Why so many `Option`s?
//! `None` represents nothing in the [Reader] buffer. This happens if no lines have been read or if EOF has been reached. It is possible to squint and avoid using `Option`. For example, [Reader::is_empty_line()] could be `false` rather than `None`. The advantage of that squint is that you don't have to deal with `Option` all the time (it is annoying). The disadvantage is that you don't have to deal with EOF explicitly. Even if there was a `is_eof()` function, it would be up to me to remember to check. `Option` forces that check, even if it is only to call `unwrap` (which, for the record, is not done). Explicit is better. The neat thing is that the `Option` design feeds in nicely into the [FirstPass][crate::FirstPass] and [SecondPass][crate::SecondPass] iterators.

use crate::parts::{ACommand, CCommand};
use crate::Assembly;
use hack_interface;

/// Low level reader of .asm files.
///
/// If you want full control over reading. [crate::FirstPass] and [crate::SecondPass] offer simpler abstractions for parsing .asm files.
pub struct Reader<R> {
    inner: R,
    buffer: Option<String>,
    pub(super) line: usize,
}

impl<R: std::io::BufRead> Reader<R> {
    /// Reader starts at the first line of the file
    pub fn new(inner: R) -> Self {
        Self {
            inner,
            buffer: None,
            line: 0,
        }
    }

    /// Read the next line into the buffer and [cleans][clean_line] it. Returns true if line was read and false if EOF was reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\nlife //carefully";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    /// );
    /// assert_eq!((a, b, c, d), (1, 3, 5, 0));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_instruction(&mut self) -> Result<usize, hack_interface::Error> {
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
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
    /// let (a, b, c) = (
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    /// );
    /// assert_eq!((a, b, c), (2, 4, 0));
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn read_command(&mut self) -> Result<usize, hack_interface::Error> {
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
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
        self.buffer.as_ref().map(|s| s.starts_with('@'))
    }
    /// Is the current line an C command (contains `'='` or `';'`)?
    ///
    /// # Examples
    /// ```
    /// let rom = b"Yes=\n;Yes\nNo";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
        self.buffer
            .as_ref()
            .map(|s| s.find(|c| c == ';' || c == '=').is_some())
    }

    /// Has anything been read into the buffer?
    ///
    /// Will be true before anything has been read or EOF has been reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"@100";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
    /// assert!(reader.is_empty_buffer());
    /// reader.read_line()?;
    /// assert!(!reader.is_empty_buffer());
    /// reader.read_line()?;
    /// assert!(reader.is_empty_buffer());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn is_empty_buffer(&self) -> bool {
        self.buffer.is_none()
    }

    /// Is the current line empty?
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\n//life //carefully";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(true));
    /// # Ok::<(), hack_interface::Error>(())
    ///
    /// ```
    pub fn is_empty_line(&self) -> Option<bool> {
        self.buffer.as_ref().map(|s| s.is_empty())
    }

    /// Is the current line a label symbol (starts with `'('`)?
    ///
    /// A label symbol is bound to the instruction memory location holding the next command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"(Yes\nNo";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
        self.buffer.as_ref().map(|s| s.starts_with('('))
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
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
                || !s
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
    /// use hack_assembler::parts::ACommand;
    /// let rom = b"@100\n@Symbol\n@SP";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
    ///     ACommand::Reserved(hack_assembler::parts::ReservedSymbols::SP)
    /// );
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn parse_a_command(&self) -> Result<ACommand, hack_interface::Error> {
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
    /// use hack_assembler::parts::{CCommand, CDest, CComp, CJump};
    /// let rom = b"M=D+A;JGE";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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
    /// use hack_assembler::parts::{ACommand, CCommand, CDest, CComp, CJump};
    /// use hack_assembler::Assembly;
    /// let rom = b"(Now)\n//Comment\n@100\nM=D+A;JGE";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
    /// let mut lines = reader.assembly_lines();
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     Assembly::Label("Now".to_string())
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     Assembly::Empty
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     Assembly::A(ACommand::Address(100))
    /// );
    /// assert_eq!(
    ///     lines.next().unwrap().unwrap(),
    ///     Assembly::C(CCommand::new(CDest::M, CComp::DPlusA, CJump::GreaterEqual))
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
    /// use hack_assembler::io::FirstPassLine;
    /// let rom = b"//Comment\n(Now)\n@100";
    /// let mut reader = hack_assembler::io::Reader::new(&rom[..]);
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

/// An iterator over assembly lines. Create with [Reader::assembly_lines()].
pub struct AssemblyLines<R> {
    inner: Reader<R>,
}

impl<R: std::io::BufRead> std::iter::Iterator for AssemblyLines<R> {
    type Item = Result<Assembly, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.read_line() {
            Ok(false) => return None,
            Ok(true) => {}
            Err(e) => return Some(Err(e)),
        };
        if self.inner.is_empty_line().unwrap() {
            Some(Ok(Assembly::Empty))
        } else if self.inner.is_label().unwrap() {
            let label = match self.inner.parse_label() {
                Ok(s) => s,
                Err(e) => return Some(Err(e)),
            };
            Some(Ok(Assembly::Label(label)))
        } else if self.inner.is_a_command().unwrap() {
            match self.inner.parse_a_command() {
                Ok(a) => Some(Ok(Assembly::A(a))),
                Err(e) => Some(Err(e)),
            }
        } else if self.inner.is_c_command().unwrap() {
            match self.inner.parse_c_command() {
                Ok(c) => Some(Ok(Assembly::C(c))),
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

impl std::convert::From<Assembly> for FirstPassLine {
    fn from(value: Assembly) -> Self {
        match value {
            Assembly::Empty => Self::Empty,
            Assembly::Label(s) => Self::Label(s),
            Assembly::C(_) => Self::Command,
            Assembly::A(_) => Self::Command,
        }
    }
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
/// use hack_assembler::io::clean_line;
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

#[cfg(test)]
mod assembly_io_tests {
    use super::*;
    use crate::parts::*;
    #[test]
    fn test_parse_c_command() -> Result<(), hack_interface::Error> {
        let rom = b"!A;JMP\nD=M-D";
        let mut reader = Reader::new(&rom[..]);
        reader.read_line()?;
        let mut c = reader.parse_c_command()?;
        assert_eq!(c, CCommand::new_jump(CComp::NotA, CJump::Jump));
        assert_eq!(hack_interface::Bit16::from(c), "1110110001000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(c, CCommand::new_dest(CDest::D, CComp::MMinusD));
        assert_eq!(hack_interface::Bit16::from(c), "1111000111010000".parse()?);
        Ok(())
    }

    #[test]
    /// 0 if calculation refers to A register, 1 if calculation refers to value of M
    fn test_c_command_flag() -> Result<(), hack_interface::Error> {
        let rom = b"0;JMP\nA;JMP\nM;JMP";
        let mut reader = crate::io::Reader::new(&rom[..]);
        reader.read_line()?;
        let mut c = reader.parse_c_command()?;
        assert_eq!(c, CCommand::new_jump(CComp::Zero, CJump::Jump));
        assert_eq!(hack_interface::Bit16::from(c), "1110101010000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(c, CCommand::new_jump(CComp::A, CJump::Jump));
        assert_eq!(hack_interface::Bit16::from(c), "1110110000000111".parse()?);
        reader.read_line()?;
        c = reader.parse_c_command()?;
        assert_eq!(c, CCommand::new_jump(CComp::M, CJump::Jump));
        assert_eq!(hack_interface::Bit16::from(c), "1111110000000111".parse()?);
        Ok(())
    }
}
