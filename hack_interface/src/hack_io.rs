//! IO of the text based `.hack` files.
//!
//! The file contains 0 or more lines. Each line consists of 16 `0` or `1` characters. Leading and trailing white spaces are ignored.
//!

/// Reader for a text based `.hack` file.
pub struct Reader<R> {
    inner: R,
    line_buffer: String,
}

impl<R: std::io::BufRead> Reader<R> {
    /// Create a new reader.
    ///
    /// # Examples
    /// ```
    /// use hack_interface::hack_io::Reader;
    /// let hack = b"0110000011001010\n1100111101100000";
    /// let mut reader = Reader::new(&hack[..]);
    /// ```
    pub fn new(buf: R) -> Self {
        Self {
            inner: buf,
            line_buffer: String::with_capacity(18),
        }
    }

    /// Reads the next instruction
    ///
    /// If End of File has been reached, returns `None`
    ///
    /// # Examples
    /// ```
    /// use hack_interface::hack_io::Reader;
    /// let hack = b"0110000011001010\n1100111101100000";
    /// let mut reader = Reader::new(&hack[..]);
    /// assert_eq!(reader.read_instruction().unwrap(), Some("0110000011001010".parse().unwrap()));
    /// assert_eq!(reader.read_instruction().unwrap(), Some("1100111101100000".parse().unwrap()));
    /// assert_eq!(reader.read_instruction().unwrap(), None);
    /// ```
    pub fn read_instruction(&mut self) -> Result<Option<crate::Bit16>, crate::Error> {
        self.line_buffer.clear();
        let read = self.inner.read_line(&mut self.line_buffer)?;

        if read == 0 {
            Ok(None)
        } else {
            let instruction_str = self.line_buffer.trim();
            let instruction = instruction_str.parse()?;
            Ok(Some(instruction))
        }
    }

    /// Returns iterator over the instructions in a file.
    ///
    /// # Examples
    /// ```
    /// use hack_interface::hack_io::Reader;
    /// let hack = b"0110000011001010\n1100111101100000";
    /// let mut reader = Reader::new(&hack[..]);
    /// let mut iter = reader.instructions();
    /// assert_eq!(iter.next().transpose().unwrap(), Some("0110000011001010".parse().unwrap()));
    /// assert_eq!(iter.next().transpose().unwrap(), Some("1100111101100000".parse().unwrap()));
    /// assert_eq!(iter.next().transpose().unwrap(), None);
    /// ```
    pub fn instructions(&mut self) -> Instructions<R> {
        Instructions::new(self)
    }
}

/// Iterates over the instructions in a file.
///
/// Create by calling [Reader::instructions]
pub struct Instructions<'a, R> {
    inner: &'a mut Reader<R>,
}

impl<'a, R: std::io::BufRead> Instructions<'a, R> {
    fn new(inner: &'a mut Reader<R>) -> Self {
        Self { inner }
    }
}

impl<'a, R: std::io::BufRead> std::iter::Iterator for Instructions<'a, R> {
    type Item = Result<crate::Bit16, crate::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.read_instruction() {
            Ok(None) => None,
            Ok(Some(i)) => Some(Ok(i)),
            Err(e) => Some(Err(e)),
        }
    }
}

/// Write [crate::Bit16] as the 0 and 1 string representation into any Write type.
///
/// Useful for writing into a vector for debugging or into a file for strage.
pub struct Writer<W> {
    inner: W,
}

impl<W: std::io::Write> Writer<W> {
    pub fn new(inner: W) -> Self {
        Self { inner }
    }

    /// Write a single instruction
    ///
    /// # Examples
    /// ```
    /// let mut w = hack_interface::hack_io::Writer::new(Vec::new());
    /// w.write_instruction(42);
    /// assert_eq!(w.as_ref(), &b"0000000000101010\n".to_vec());
    /// ```
    pub fn write_instruction(
        &mut self,
        instruction: impl Into<crate::Bit16>,
    ) -> Result<(), crate::Error> {
        writeln!(self.inner, "{}", instruction.into())?;
        Ok(())
    }
}

impl<W> std::convert::AsRef<W> for Writer<W> {
    fn as_ref(&self) -> &W {
        &self.inner
    }
}
