//! Reader for .vm files.

pub struct Reader<R> {
    inner: R,
    buffer: Option<Vec<String>>,
    line: u16,
}

impl<R: std::io::BufRead> Reader<R> {
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
    /// let input = b"Create\nlife //carefully";
    /// let mut reader = hack_virtual_machine::reader::Reader::new(&input[..]);
    /// let (a, b, c, d) = (
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    ///     reader.read_line()?,
    /// );
    /// assert_eq!((a, b, c, d), (true, true, false, false));
    /// # Ok::<(), hack_virtual_machine::Error>(())
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
            let v: Vec<String> = temp
                .split_ascii_whitespace()
                .map(|x| x.to_string())
                .collect();
            self.buffer = Some(v);
            Ok(true)
        }
    }

    /// What command is currently in the buffer.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, CommandType, Arithmetic};
    /// let input = b"\n//Nothing line\nadd \nweird";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.check_command(), Some(CommandType::EmptyLine));
    /// reader.read_line()?;
    /// assert_eq!(reader.check_command(), Some(CommandType::EmptyLine));
    /// reader.read_line()?;
    /// assert_eq!(reader.check_command(), Some(CommandType::Arithmetic(Arithmetic::Add)));
    /// reader.read_line()?;
    /// assert_eq!(reader.check_command(), Some(CommandType::Invalid));
    /// reader.read_line()?;
    /// assert_eq!(reader.check_command(), None);
    /// # Ok::<(), hack_virtual_machine::Error>(())
    /// ```
    pub fn check_command(&self) -> Option<CommandType> {
        match &self.buffer {
            None => None,
            Some(v) => {
                if let Some(s) = v.get(0) {
                    let com = match s.as_str() {
                        "add" => CommandType::Arithmetic(Arithmetic::Add),
                        "sub" => CommandType::Arithmetic(Arithmetic::Subtract),
                        "neg" => CommandType::Arithmetic(Arithmetic::Negative),
                        "eq" => CommandType::Arithmetic(Arithmetic::Equal),
                        "gt" => CommandType::Arithmetic(Arithmetic::GreaterThan),
                        "lt" => CommandType::Arithmetic(Arithmetic::LessThan),
                        "and" => CommandType::Arithmetic(Arithmetic::BitAnd),
                        "or" => CommandType::Arithmetic(Arithmetic::BitOr),
                        "not" => CommandType::Arithmetic(Arithmetic::BitNot),
                        "push" => CommandType::Push,
                        "pop" => CommandType::Pop,
                        "label" => CommandType::Label,
                        "goto" => CommandType::Goto,
                        "if-goto" => CommandType::If,
                        "function" => CommandType::Function,
                        "call" => CommandType::Call,
                        "return" => CommandType::Return,
                        _ => CommandType::Invalid,
                    };
                    Some(com)
                } else {
                    Some(CommandType::EmptyLine)
                }
            }
        }
    }

    /// Returns error if buffer does not have the expected number of fields (command + args).
    ///
    /// If nothing is in the buffer, returns `Ok`.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader};
    /// let input = b"Three args here";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert!(reader.error_buffer_len(3).is_ok());
    /// assert!(reader.error_buffer_len(2).is_err());
    /// reader.read_line()?;
    /// assert!(reader.error_buffer_len(3).is_ok());
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn error_buffer_len(&self, len: usize) -> Result<(), crate::Error> {
        if let Some(buf) = &self.buffer {
            if buf.len() == len {
                Ok(())
            } else {
                Err(crate::Error::InvalidArgs(self.line))
            }
        } else {
            Ok(())
        }
    }

    /// Parse the segment and index arg of a push or pop command.
    ///
    /// This assumes the line is at an push or pop command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Segment};
    /// let input = b"push_or_pop static 3";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_args_push_pop()?, Some((Segment::Static, 3)));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_args_push_pop(&self) -> Result<Option<(Segment, u16)>, crate::Error> {
        if let Some(buf) = &self.buffer {
            let s = buf
                .get(1)
                .ok_or(crate::Error::InvalidArgs(self.line))?
                .parse()
                .or(Err(crate::Error::InvalidArgs(self.line)))?;
            let i = buf
                .get(2)
                .ok_or(crate::Error::InvalidArgs(self.line))?
                .parse()
                .or(Err(crate::Error::InvalidArgs(self.line)))?;
            Ok(Some((s, i)))
        } else {
            Ok(None)
        }
    }

    /// Parse the symbol arg.
    ///
    /// Assumes the line has a symbol as the first arg.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::Reader;
    /// let input = b"command symbol_is_best";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_args_symbol()?, Some(&"symbol_is_best".to_string()));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_args_symbol(&self) -> Result<Option<&String>, crate::Error> {
        if let Some(buf) = &self.buffer {
            Ok(Some(
                buf.get(1).ok_or(crate::Error::InvalidArgs(self.line))?,
            ))
        } else {
            Ok(None)
        }
    }

    /// Parse an arithmetic command.
    ///
    /// This assumes the line is at the arithmetic command specified to the function.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command, Arithmetic};
    /// let input = b"just_one_command";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_arithmetic(Arithmetic::Add)?, Some(Command::Arithmetic(Arithmetic::Add)));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_arithmetic(
        &self,
        kind: Arithmetic,
    ) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(1)?;
        match &self.buffer {
            Some(_) => Ok(Some(Command::Arithmetic(kind))),
            None => Ok(None),
        }
    }

    /// Parse a goto command.
    ///
    /// Assumes line is at a goto command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command};
    /// let input = b"com_not_checked give_me_a_symbol";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_goto()?, Some(Command::Goto("give_me_a_symbol".to_string())));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_goto(&self) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(2)?;
        match self.parse_args_symbol()? {
            Some(s) => Ok(Some(Command::Goto(s.to_owned()))),
            None => Ok(None),
        }
    }

    /// Parse a if command.
    ///
    /// Assumes line is at a if command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command};
    /// let input = b"com_not_checked give_me_a_symbol";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_if()?, Some(Command::If("give_me_a_symbol".to_string())));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_if(&self) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(2)?;
        match self.parse_args_symbol()? {
            Some(s) => Ok(Some(Command::If(s.to_owned()))),
            None => Ok(None),
        }
    }

    /// Parse a label command.
    ///
    /// Assumes line is at a label command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command};
    /// let input = b"label_com_not_checked give_me_a_symbol";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_label()?, Some(Command::Label("give_me_a_symbol".to_string())));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_label(&self) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(2)?;
        match self.parse_args_symbol()? {
            Some(s) => Ok(Some(Command::Label(s.to_owned()))),
            None => Ok(None),
        }
    }

    /// Parse the pop command.
    ///
    /// Assumes the line is on a pop command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command, Segment};
    /// let input = b"does_not_matter temp 4";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_pop()?, Some(Command::Pop(Segment::Temp, 4)));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_pop(&self) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(3)?;
        if let Some((s, i)) = self.parse_args_push_pop()? {
            Ok(Some(Command::Pop(s, i)))
        } else {
            Ok(None)
        }
    }

    /// Parse the push command.
    ///
    /// Assumes the line is on a push command.
    ///
    /// # Examples
    /// ```
    /// use hack_virtual_machine::reader::{Reader, Command, Segment};
    /// let input = b"does_not_matter local 2";
    /// let mut reader = Reader::new(&input[..]);
    /// reader.read_line()?;
    /// assert_eq!(reader.parse_command_push()?, Some(Command::Push(Segment::Local, 2)));
    /// # Ok::<(), hack_virtual_machine::Error>(())
    pub fn parse_command_push(&self) -> Result<Option<Command>, crate::Error> {
        self.error_buffer_len(3)?;
        if let Some((s, i)) = self.parse_args_push_pop()? {
            Ok(Some(Command::Push(s, i)))
        } else {
            Ok(None)
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Command {
    Arithmetic(Arithmetic),
    Goto(String),
    If(String),
    Label(String),
    Pop(Segment, u16),
    Push(Segment, u16),
}

/// The commands that the VM supports.
///
/// The extra ones needed for my implementation are
/// * `EmptyLine`: a line that is empty (or comment only) and does nothing
/// * `Invalid`: a line that has an unknown command
#[derive(Debug, PartialEq, Eq)]
pub enum CommandType {
    Arithmetic(Arithmetic),
    Push,
    Pop,
    Label,
    Goto,
    If,
    Function,
    Return,
    Call,
    EmptyLine,
    Invalid,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Arithmetic {
    Add,
    Subtract,
    Negative,
    Equal,
    GreaterThan,
    LessThan,
    BitAnd,
    BitOr,
    BitNot,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Segment {
    Argument,
    Local,
    Static,
    Constant,
    This,
    That,
    Pointer,
    Temp,
}

impl std::str::FromStr for Segment {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "argument" => Ok(Segment::Argument),
            "local" => Ok(Segment::Local),
            "static" => Ok(Segment::Static),
            "constant" => Ok(Segment::Constant),
            "this" => Ok(Segment::This),
            "that" => Ok(Segment::That),
            "pointer" => Ok(Segment::Pointer),
            "temp" => Ok(Segment::Temp),
            _ => Err(()),
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
