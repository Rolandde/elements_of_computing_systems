//! Reader for .vm files.

use crate::{Command, Error};

/// Reader that converts .vm files into [Command]s.
///
/// For each line, the reader determines how many args there are and populates the appropriate fields. It is up to the consumer to check arg numbers before parsing the fields. Using fields above the number read will get you fields from a previous line.
///
/// The safer implementation would be to use vector and options, but requires checking all elements and dealing with lots of match statements. With the arg number approach, one (non-enforced) check (how many args are there) provides all the guarantees.
///
pub struct Reader<R> {
    inner: R,
    buffer: String,
    args: u8,
    cmd: String,
    arg2: String,
    arg3: u16,
    line: usize,
}

impl<R: std::io::BufRead> Reader<R> {
    pub fn new(inner: R) -> Self {
        Self {
            inner,
            buffer: "".to_string(),
            args: 0,
            cmd: "".to_string(),
            arg2: "".to_string(),
            arg3: 0,
            line: 0,
        }
    }

    /// Read the next line into the buffer and [cleans][clean_line] it.
    ///
    /// Returns the total number of lines read so far. Returns 0 if EOF has been reached.
    ///
    /// # Examples
    /// ```
    /// let input = b"Create\nlife //carefully";
    /// let mut reader = hack_virtual_machine::reader::Reader::new(&input[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    /// );
    /// assert_eq!((a, b, c, d), (1, 2, 0, 0));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    /// ```
    pub fn read_line(&mut self) -> Result<usize, Error> {
        self.buffer.clear();
        let read = self.inner.read_line(&mut self.buffer)?;
        if read == 0 {
            Ok(0)
        } else {
            clean_line(&mut self.buffer);
            self.args = 0;
            self.line += 1;
            let mut a = self.buffer.split_ascii_whitespace();

            match a.next() {
                None => return Ok(self.line),
                Some(s) => {
                    self.cmd.clear();
                    self.cmd.push_str(s);
                    self.args += 1;
                }
            };

            match a.next() {
                None => return Ok(self.line),
                Some(s) => {
                    self.arg2.clear();
                    self.arg2.push_str(s);
                    self.args += 1;
                }
            };

            match a.next() {
                None => return Ok(self.line),
                Some(s) => {
                    self.arg3 = s.parse().or(Err(Error::InvalidArgs(self.line)))?;
                    self.args += 1;
                }
            };

            match a.next() {
                None => Ok(self.line),
                Some(_) => Err(Error::InvalidArgs(self.line)),
            }
        }
    }

    /// Read the next [cleaned][clean_line] command line into the buffer.
    ///
    /// This will skip empty lines and comment only lines.
    ///
    /// Returns the line number of the command or 0 if EOF has been reached.
    ///
    /// # Examples
    /// ```
    /// let input = b"// Create\n\nlife \njoyfully\n";
    /// let mut reader = hack_virtual_machine::reader::Reader::new(&input[..]);
    /// let (a, b, c) = (
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    ///     reader.read_command()?,
    /// );
    /// assert_eq!((a, b, c), (3, 4, 0));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    /// ```
    pub fn read_command(&mut self) -> Result<usize, Error> {
        let mut line = self.read_line()?;

        while line != 0 && self.args == 0 {
            line = self.read_line()?;
        }

        Ok(line)
    }

    /// Parse the command currently in the buffer.
    ///
    /// This assumes there is a command line in the buffer.
    ///
    /// # Examples
    /// ```
    /// let input = b"//My program\nadd\n\nnot";
    /// let mut reader = hack_virtual_machine::reader::Reader::new(&input[..]);
    /// reader.read_command()?;
    /// let add = reader.parse_command()?;
    /// assert_eq!(add, hack_virtual_machine::Command::Add);
    /// reader.read_command()?;
    /// let not = reader.parse_command()?;
    /// assert_eq!(not, hack_virtual_machine::Command::BitNot);
    /// # Ok::<(), hack_virtual_machine::Error>(())
    /// ```
    pub fn parse_command(&mut self) -> Result<Command, Error> {
        match self.cmd.as_str() {
            "add" => {
                self.assert_args(1)?;
                Ok(Command::Add)
            }
            "sub" => {
                self.assert_args(1)?;
                Ok(Command::Subtract)
            }
            "neg" => {
                self.assert_args(1)?;
                Ok(Command::Negative)
            }
            "eq" => {
                self.assert_args(1)?;
                Ok(Command::Equal)
            }
            "gt" => {
                self.assert_args(1)?;
                Ok(Command::GreaterThan)
            }
            "lt" => {
                self.assert_args(1)?;
                Ok(Command::LessThan)
            }
            "and" => {
                self.assert_args(1)?;
                Ok(Command::Add)
            }
            "or" => {
                self.assert_args(1)?;
                Ok(Command::BitOr)
            }
            "not" => {
                self.assert_args(1)?;
                Ok(Command::BitNot)
            }
            "push" => {
                self.assert_args(3)?;
                Ok(Command::Push(
                    self.arg2
                        .parse()
                        .or(Err(Error::UnknownSegment(self.line)))?,
                    self.arg3,
                ))
            }
            "pop" => {
                self.assert_args(3)?;
                Ok(Command::Pop(
                    self.arg2
                        .parse()
                        .or(Err(Error::UnknownSegment(self.line)))?,
                    self.arg3,
                ))
            }
            _ => Err(Error::UnknownCommand(self.line)),
        }
    }

    fn assert_args(&self, num: u8) -> Result<(), Error> {
        if num != self.args {
            Err(Error::InvalidArgs(self.line))
        } else {
            Ok(())
        }
    }
}

/// Remove leading and trailing whitespace and any comment characters. May leave an empty string.
///
/// Comment characters are those following `"//"` (including itself).
///
/// # Examples
/// ```
/// use hack_virtual_machine::reader::clean_line;
/// let mut s = " No whitespace    ".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "No whitespace".to_string());
/// let mut s = " Code //Comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "Code".to_string());
/// s = " // Double // Comment".to_string();
/// clean_line(&mut s);
/// assert_eq!(s, "".to_string());
/// ```
pub fn clean_line(line: &mut String) {
    let no_comments = match line.split_once("//") {
        None => line.to_string(),
        Some((instruction, _)) => instruction.to_string(),
    };
    let no_white_space = no_comments.trim();
    line.clear();
    line.push_str(no_white_space);
}

#[cfg(test)]
mod vm_parser_tests {
    use super::*;

    #[test]
    fn test_empty() -> Result<(), Error> {
        let input = b"\n//Empty\n     \n";
        let mut reader = Reader::new(&input[..]);
        assert_eq!(0, reader.read_command()?);
        reader = Reader::new(b"");
        assert_eq!(0, reader.read_command()?);
        Ok(())
    }

    #[test]
    fn test_algorithm() -> Result<(), Error> {
        let input = b"sub";
        let mut reader = Reader::new(&input[..]);
        reader.read_command()?;
        assert_eq!(reader.parse_command()?, Command::Subtract);
        Ok(())
    }

    #[test]
    fn test_segment() -> Result<(), Error> {
        let input = b"push local 3";
        let mut reader = Reader::new(&input[..]);
        reader.read_command()?;
        assert_eq!(
            reader.parse_command()?,
            Command::Push(crate::Segment::Local, 3)
        );
        Ok(())
    }
}
