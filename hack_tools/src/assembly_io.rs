//! IO for assembly (.asm) files
//!
//! # FAQ
//!
//! ## Why `i16` for line counting?
//! The [hack_kernel::Computer] and the [ROM][hack_kernel::Rom32K] use a 15 bit address space. Although an .asm file (which is loaded in the ROM) could contain more lines than can be expressed by 15 bits (greater than 32767), the extra lines would not fit into the ROM. By using `i16` and starting from 0 (first bit is always 0), one gets a very convenient representation of a 15 bit address space. [crate::Bit15] contains a check for negative numbers, so will panic if integer overflow happens.

/// Low level reader of .asm files.
///
/// If you want full control over reading. [crate::assembly::FirstPass] and [crate::assembly::SecondPass] offer simpler abstractions for parsing .asm files.
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

    /// Read the next line into the buffer and [clean][clean_line] it. Returns true if line was read and false if EOF was reached.
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\nlife \\carefully";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    /// );
    /// assert_eq!((a, b, c, d), (true, true, false, false));
    /// # Ok::<(), hack_tools::Error>(())
    /// ```
    pub fn read_line(&mut self) -> Result<bool, crate::Error> {
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
    /// let rom = b"I\n\nlike\n\\me\nyou";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    ///     reader.read_instruction()?,
    /// );
    /// assert_eq!((a, b, c, d), (1, 3, 5, 0));
    /// # Ok::<(), hack_tools::Error>(())
    /// ```
    pub fn read_instruction(&mut self) -> Result<i16, crate::Error> {
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

    /// Is the current line a command (A or C)
    ///
    /// # Examples
    /// ```
    /// let rom = b"@Yes\nYes;\nNo";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_command(), Some(false));
    /// # Ok::<(), hack_tools::Error>(())
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
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_a_command(), None);
    /// # Ok::<(), hack_tools::Error>(())
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
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_c_command(), None);
    /// # Ok::<(), hack_tools::Error>(())
    ///
    /// ```
    pub fn is_c_command(&self) -> Option<bool> {
        match &self.buffer {
            None => None,
            Some(s) => Some(s.find(|c| c == ';' || c == '=').is_some()),
        }
    }

    /// Is the current line empty?
    ///
    /// # Examples
    /// ```
    /// let rom = b"Create\n\\life \\carefully";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_empty_line(), Some(true));
    /// # Ok::<(), hack_tools::Error>(())
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
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), Some(true));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), Some(false));
    /// reader.read_line()?;
    /// assert_eq!(reader.is_label(), None);
    /// # Ok::<(), hack_tools::Error>(())
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
    /// This assumes the current line is a label.
    ///
    /// # Examples
    /// ```
    /// let rom = b"(Yes)";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_label()?, Some("Yes".to_string()));
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_label()?, None);
    /// # Ok::<(), hack_tools::Error>(())
    /// ```
    pub fn parse_label(&self) -> Result<Option<String>, crate::Error> {
        if let Some(a) = &self.buffer {
            if !a.starts_with('(') || !a.ends_with(')') {
                Err(crate::Error::AssemblyLabel(self.line))
            } else {
                let s = a
                    .get(1..a.len() - 1)
                    .ok_or(crate::Error::AssemblyLabel(self.line))?;
                Ok(Some(s.to_string()))
            }
        } else {
            Ok(None)
        }
    }

    /// Parse an A-command.
    ///
    /// This assumes the current line is an A-command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"@010011010011100\n@Symbol";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_a_command()?,
    ///     hack_tools::assembly_io::SplitACommand::Address("010011010011100".parse()?)
    /// );
    ///
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_a_command()?,
    ///     hack_tools::assembly_io::SplitACommand::Symbol("Symbol".to_string())
    /// );
    /// # Ok::<(), hack_tools::Error>(())
    /// ```
    pub fn parse_a_command(&self) -> Result<SplitACommand, crate::Error> {
        use std::str::FromStr;
        let line = self.line;
        let a = self.buffer.as_ref().ok_or(crate::Error::ACommand(line))?;
        let first = a.chars().next().ok_or(crate::Error::ACommand(line))?;
        if first != '@' {
            Err(crate::Error::ACommand(line))
        } else {
            let s = a.get(1..).ok_or(crate::Error::ACommand(line))?;
            if s.starts_with(|c: char| c.is_digit(10)) {
                Ok(SplitACommand::Address(
                    crate::Bit15::from_str(s).map_err(|_| crate::Error::ACommand(line))?,
                ))
            } else {
                Ok(SplitACommand::Symbol(s.to_string()))
            }
        }
    }

    /// Parse an C-command.
    ///
    /// This assumes the current line is an C-command.
    ///
    /// # Examples
    /// ```
    /// let rom = b"M=D+A;JGE";
    /// let mut reader = hack_tools::assembly_io::Reader::new(&rom[..]);
    /// reader.read_line()?;
    /// assert_eq!(
    ///     reader.parse_c_command()?,
    ///     "1110000010001011".parse()?
    /// );
    /// # Ok::<(), hack_tools::Error>(())
    /// ```
    ///
    pub fn parse_c_command(&self) -> Result<crate::Bit16, crate::Error> {
        let line = self.line;
        let str_command = self.buffer.as_ref().ok_or(crate::Error::CCommand(line))?;
        let (destination_str, rest) = match str_command.split_once("=") {
            Some((d, r)) => (Some(d), r),
            None => (None, str_command.as_ref()),
        };
        let destination = if let Some(d) = destination_str {
            match d {
                "M" => Ok([false, false, true]),
                "D" => Ok([false, true, false]),
                "MD" => Ok([false, true, true]),
                "A" => Ok([true, false, false]),
                "AM" => Ok([true, false, true]),
                "AD" => Ok([true, true, false]),
                "AMD" => Ok([true, true, true]),
                _ => Err(crate::Error::CCommand(line)),
            }
        } else {
            Ok([false, false, false])
        }?;

        let (command_str, jump_str) = match rest.split_once(";") {
            Some((c, j)) => (c, Some(j)),
            None => (rest, None),
        };

        let jump = if let Some(j) = jump_str {
            match j {
                "JGT" => Ok([false, false, true]),
                "JEQ" => Ok([false, true, false]),
                "JGE" => Ok([false, true, true]),
                "JLT" => Ok([true, false, false]),
                "JNE" => Ok([true, false, true]),
                "JLE" => Ok([true, true, false]),
                "JMP" => Ok([true, true, true]),
                _ => Err(crate::Error::CCommand(line)),
            }
        } else {
            Ok([false, false, false])
        }?;

        let a_flag = if command_str.contains("A") {
            false
        } else {
            true
        };
        // Allocate a new string (bad), but cut down on comparisons (good)
        let a_command = command_str.replace("M", "A");
        let command = match a_command.as_ref() {
            "0" => Ok(hack_kernel::arithmetic::ALU_ZERO),
            "1" => Ok(hack_kernel::arithmetic::ALU_ONE),
            "-1" => Ok(hack_kernel::arithmetic::ALU_MINUS_ONE),
            "D" => Ok(hack_kernel::arithmetic::ALU_X),
            "A" => Ok(hack_kernel::arithmetic::ALU_Y),
            "!D" => Ok(hack_kernel::arithmetic::ALU_X_NOT),
            "!A" => Ok(hack_kernel::arithmetic::ALU_Y_NOT),
            "-D" => Ok(hack_kernel::arithmetic::ALU_X_MINUS),
            "-A" => Ok(hack_kernel::arithmetic::ALU_Y_MINUS),
            "D+1" => Ok(hack_kernel::arithmetic::ALU_X_PLUS1),
            "A+1" => Ok(hack_kernel::arithmetic::ALU_Y_PLUS1),
            "D-1" => Ok(hack_kernel::arithmetic::ALU_X_MINUS1),
            "A-1" => Ok(hack_kernel::arithmetic::ALU_Y_MINUS1),
            "D+A" => Ok(hack_kernel::arithmetic::ALU_X_PLUS_Y),
            "D-A" => Ok(hack_kernel::arithmetic::ALU_X_MINUS_Y),
            "A-D" => Ok(hack_kernel::arithmetic::ALU_Y_MINUS_X),
            "D&A" => Ok(hack_kernel::arithmetic::ALU_X_AND_Y),
            "D|A" => Ok(hack_kernel::arithmetic::ALU_X_OR_Y),
            _ => Err(crate::Error::CCommand(line)),
        }?;

        Ok(crate::Bit16 {
            i: [
                true,
                true,
                true,
                a_flag,
                command[0],
                command[1],
                command[2],
                command[3],
                command[4],
                command[5],
                destination[0],
                destination[1],
                destination[2],
                jump[0],
                jump[1],
                jump[2],
            ],
        })
    }
}

/// Remove all white space and comment characters. May leave an empty string.
///
/// Comment characters are those following `"\\"` (including itself).
///
/// # Examples
/// ```
/// use hack_tools::assembly_io::clean_line;
/// let mut s = "in st \\spaces and trailing comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "inst".to_string());
/// clean_line(&mut s);
/// assert_eq!(s, "inst".to_string());
/// s = "\\ Starting comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "".to_string());
/// ```
pub fn clean_line(line: &mut String) {
    line.retain(|c| !c.is_whitespace());
    let no_comments = match line.split_once("\\") {
        None => line.to_string(),
        Some((instruction, _)) => instruction.to_string(),
    };
    line.clear();
    line.push_str(&no_comments);
}

/// A parsed A-command can be either an address or a symbol
#[derive(Debug, PartialEq, Eq)]
pub enum SplitACommand {
    Address(crate::Bit15),
    Symbol(String),
}
