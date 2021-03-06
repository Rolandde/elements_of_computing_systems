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
    /// use hack_tools::hack_io::Reader;
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
    /// use hack_tools::hack_io::Reader;
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
    /// use hack_tools::hack_io::Reader;
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

/// Write [crate::Bit16] as the 0 and 1 representation.
pub struct Writer<W> {
    inner: W
}

impl<W: std::io::Write> Writer<W> {
    pub fn new(inner: W) -> Self {
        Self {inner}
    }

    /// Write a single instruction
    /// 
    /// # Examples
    /// ```
    /// let mut w = hack_tools::hack_io::Writer::new(Vec::new());
    /// let bit_42 = 42.into();
    /// w.write_instruction(&bit_42);
    /// assert_eq!(w.as_ref(), &b"0000000000101010\n".to_vec());
    /// ```
    pub fn write_instruction(&mut self, instruction: &crate::Bit16) -> Result<(), crate::Error> {
        writeln!(self.inner, "{}", instruction)?;
        Ok(())
    }
}

impl<W> std::convert::AsRef<W> for Writer<W> {
    fn as_ref(&self) -> &W {
        &self.inner
    }
}

/// Create a ROM from a buffer that holds instructions in `.hack` format
///
/// # Examples
/// ```
/// use hack_tools::hack_io::write_rom_from_buffer;
/// use hack_kernel::Computer;
/// let input = b"0110001111001010\n1111000011110000";
/// let rom = write_rom_from_buffer(&input[..]);
/// let mut c = Computer::new(rom);
/// c.cycle(false);
/// ```
/// # Panics
/// On invalid instruction format. A hack computer cannot run without valid instructions, so there is no point dealing with errors. If one game cartridge won't load, but all your other games work, you either return the game cartridge or have really steady hands.
///
pub fn write_rom_from_buffer(buf: impl std::io::BufRead) -> hack_kernel::Rom32K {
    let mut writer = hack_kernel::Rom32KWriter::new();
    let mut reader = Reader::new(buf);
    for (i, instruction) in reader.instructions().enumerate() {
        let inst = instruction.unwrap_or_else(|e| panic!("Failed on line {}: {}", i + 1, e));
        writer.write_next(inst.i);
    }
    writer.create_rom()
}

/// Create a ROM from a `.hack` file
///
/// # Examples
/// ```
/// use hack_tools::hack_io::write_rom_from_file;
/// use hack_kernel::Computer;
/// // A simple `.hack` file with two lines
/// let mut d = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
/// d.push("resources/test/example.hack");
/// let rom = write_rom_from_file(d);
/// let mut c = Computer::new(rom);
/// c.cycle(false);
/// ```
///
/// # Panics
/// See panic note for [write_rom_from_buffer]
///
pub fn write_rom_from_file<P: AsRef<std::path::Path>>(path: P) -> hack_kernel::Rom32K {
    let f = std::fs::File::open(path).unwrap_or_else(|e| panic!("Cannot open file: {}", e));
    write_rom_from_buffer(std::io::BufReader::new(f))
}
