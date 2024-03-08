//! Reader for .vm files.

use crate::{Command, Error, Segment};

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
    arg3: i16,
    line: usize,
    in_func: bool, // True between starting a function and returning. Cannot start a new function while this is true.
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
            in_func: false,
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
                Ok(Command::BitAnd)
            }
            "or" => {
                self.assert_args(1)?;
                Ok(Command::BitOr)
            }
            "not" => {
                self.assert_args(1)?;
                Ok(Command::BitNot)
            }
            "push" => Ok(Command::Push(self.parse_segment()?)),
            "pop" => Ok(Command::Pop(self.parse_segment()?)),
            "label" => {
                self.assert_args(2)?;
                Ok(Command::Label(self.check_label_func()?))
            }
            "goto" => {
                self.assert_args(2)?;
                Ok(Command::Goto(self.check_label_func()?))
            }
            "if-goto" => {
                self.assert_args(2)?;
                Ok(Command::GotoIf(self.check_label_func()?))
            }
            "function" => {
                self.assert_args(3)?;
                if self.in_func {
                    Err(Error::InvalidFunction(self.line))
                } else {
                    self.in_func = true;
                    Ok(Command::Function(self.check_label_func()?, self.arg3))
                }
            }
            "call" => {
                self.assert_args(3)?;
                Ok(Command::Call(self.check_label_func()?, self.arg3))
            }
            "return" => {
                self.assert_args(1)?;
                if self.in_func {
                    self.in_func = false;
                    Ok(Command::Return)
                } else {
                    Err(Error::InvalidFunction(self.line))
                }
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

    /// Checks the label of function name and returns a copy of it.
    ///
    /// This assumes that a goto, if-goto, function, or call is in the buffer.
    fn check_label_func(&self) -> Result<String, Error> {
        if self
            .arg2
            .chars()
            .nth(0)
            .ok_or(Error::InvalidLabelFunc(self.line))?
            .is_numeric()
            || !self
                .arg2
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '.' || c == ':')
        {
            Err(Error::InvalidLabelFunc(self.line))
        } else {
            Ok(self.arg2.clone())
        }
    }

    /// Parse the segment in the buffer.
    ///
    /// Assumes there is a segment in the buffer, but does all segment validity checking.
    ///
    /// # Examples
    /// ```
    /// let input = b"push local 7";
    /// let mut reader = hack_virtual_machine::reader::Reader::new(&input[..]);
    /// reader.read_command()?;
    /// let add = reader.parse_segment()?;
    /// assert_eq!(add, hack_virtual_machine::Segment::Local(7));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    /// ```
    pub fn parse_segment(&self) -> Result<Segment, Error> {
        self.assert_args(3)?;
        let seg = self
            .arg2
            .parse()
            .or(Err(Error::UnknownSegment(self.line)))?;

        match seg {
            SegmentName::Argument => Ok(Segment::Argument(self.arg3)),
            SegmentName::Local => Ok(Segment::Local(self.arg3)),
            SegmentName::Static => Ok(Segment::Static(self.arg3)),
            SegmentName::Constant => Ok(Segment::Constant(self.arg3)),
            SegmentName::This => Ok(Segment::This(self.arg3)),
            SegmentName::That => Ok(Segment::That(self.arg3)),
            SegmentName::Pointer => match self.arg3 {
                0 => Ok(Segment::PointerThis),
                1 => Ok(Segment::PointerThat),
                _ => Err(Error::OutOfBoundsIndex(self.line)),
            },
            SegmentName::Temp => match self.arg3 {
                0 => Ok(Segment::Temp0),
                1 => Ok(Segment::Temp1),
                2 => Ok(Segment::Temp2),
                3 => Ok(Segment::Temp3),
                4 => Ok(Segment::Temp4),
                5 => Ok(Segment::Temp5),
                6 => Ok(Segment::Temp6),
                7 => Ok(Segment::Temp7),
                _ => Err(Error::OutOfBoundsIndex(self.line)),
            },
        }
    }
}

/// Iterator over virtual machine lines.
///
/// # Examples
/// ```
/// let input = b"//My program\nadd\n\nnot";
/// let mut coms = hack_virtual_machine::reader::CommandLines::new(&input[..]);
/// assert_eq!(coms.next().unwrap().unwrap(), hack_virtual_machine::Command::Add);
/// assert_eq!(coms.next().unwrap().unwrap(), hack_virtual_machine::Command::BitNot);
/// assert!(coms.next().is_none())
/// ```
pub struct CommandLines<R> {
    inner: Reader<R>,
}

impl<R: std::io::BufRead> CommandLines<R> {
    pub fn new(buffer: R) -> Self {
        Self {
            inner: Reader::new(buffer),
        }
    }
}

impl<R: std::io::BufRead> std::iter::Iterator for CommandLines<R> {
    type Item = Result<Command, Error>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.read_command() {
            Err(e) => Some(Err(e)),
            Ok(0) => None,
            Ok(_) => match self.inner.parse_command() {
                Err(e) => Some(Err(e)),
                Ok(c) => Some(Ok(c)),
            },
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

enum SegmentName {
    Argument,
    Local,
    Static,
    Constant,
    This,
    That,
    Pointer,
    Temp,
}

impl std::str::FromStr for SegmentName {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "argument" => Ok(SegmentName::Argument),
            "local" => Ok(SegmentName::Local),
            "static" => Ok(SegmentName::Static),
            "constant" => Ok(SegmentName::Constant),
            "this" => Ok(SegmentName::This),
            "that" => Ok(SegmentName::That),
            "pointer" => Ok(SegmentName::Pointer),
            "temp" => Ok(SegmentName::Temp),
            _ => Err(()),
        }
    }
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
        let input = b"push pointer 1\npop temp 4";
        let mut reader = Reader::new(&input[..]);
        reader.read_command()?;
        assert_eq!(
            reader.parse_command()?,
            Command::Push(crate::Segment::PointerThat)
        );
        reader.read_command()?;
        assert_eq!(reader.parse_command()?, Command::Pop(crate::Segment::Temp4));
        Ok(())
    }

    #[test]
    fn test_label() -> Result<(), Error> {
        let input = b"label valid\nlabel inva$lid";
        let mut reader = Reader::new(&input[..]);
        reader.read_command()?;
        assert_eq!(reader.parse_command()?, Command::Label("valid".to_string()));
        reader.read_command()?;
        assert!(reader.parse_command().is_err());
        Ok(())
    }

    #[test]
    fn test_function() -> Result<(), Error> {
        let input = b"function test.func 3";
        let mut reader = Reader::new(&input[..]);
        reader.read_command()?;
        assert_eq!(
            reader.parse_command()?,
            Command::Function("test.func".to_string(), 3)
        );
        Ok(())
    }
}
