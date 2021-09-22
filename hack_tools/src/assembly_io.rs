//! IO for assembly (.asm) files

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
                    if !b {break Ok(self.line)}
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
                let s = a.get(1..a.len() - 1).ok_or(crate::Error::AssemblyLabel(self.line))?;
                Ok(Some(s.to_string()))
            }
        } else {
            Ok(None)
        }
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
