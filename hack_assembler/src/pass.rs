//! Logic for doing first and second pass.
//!
//! [FirstPass] creates the [SymbolTable] if labels are in assembly.
//!
//! The [SecondPass] iterator wraps the [Assembler], providing all the iterator fun. [SecondPassTrusted] is an iterator that produces machine instructions without errors. Use this if you are certain assembly input contains no errors.

use crate::io::{FirstPassLine, Reader};
use crate::parts::ReservedSymbols;
use crate::{Assembler, Assembly};

/// Symbol table generated by the first pass through the assembly code.
///
/// Created by [FirstPass]. If you are certain the assembly code does not use any labels, this can be used directly with [SecondPass].
#[derive(Debug, PartialEq, Eq)]
pub struct SymbolTable {
    inner: std::collections::HashMap<String, hack_interface::Bit15>,
}

impl SymbolTable {
    /// Create an empty symbol table.
    pub fn empty() -> Self {
        Self {
            inner: std::collections::HashMap::new(),
        }
    }

    /// How many labels have been come across.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Get address of label.
    pub fn get(&self, k: &str) -> Option<hack_interface::Bit15> {
        match ReservedSymbols::try_from(k) {
            Ok(b) => Some(b.into()),
            Err(_) => self.inner.get(k).copied(),
        }
    }

    pub fn insert(&mut self, k: String, v: hack_interface::Bit15) -> Option<hack_interface::Bit15> {
        self.inner.insert(k, v)
    }

    /// Is the symbol table empty
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

/// Go through assembly and generate a [SymbolTable] that holds the labels.
pub struct FirstPass {
    inner: std::collections::HashMap<String, hack_interface::Bit15>,
    last_label: Option<String>,
    line_count: usize,
    command_count: i16,
}

impl FirstPass {
    pub fn new() -> Self {
        Self {
            inner: std::collections::HashMap::new(),
            last_label: None,
            line_count: 0,
            command_count: 0,
        }
    }

    /// Generate the symbol table from the lines read so far.
    ///
    /// Gives an error if first pass is at a label. Labels must be followed by commands.
    ///
    /// # Examples
    /// ```
    /// let nothing = Vec::new();
    /// let s = hack_assembler::FirstPass::from_slice(&nothing[..])?;
    /// assert_eq!(s, hack_assembler::SymbolTable::empty());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn create(self) -> Result<SymbolTable, hack_interface::Error> {
        match self.last_label {
            None => Ok(SymbolTable { inner: self.inner }),
            Some(_) => Err(hack_interface::Error::SymbolTable(self.line_count)),
        }
    }

    /// Create a symbol table from a line buffer.
    ///
    /// Common use is doing a first pass on a file.
    ///
    /// # Examples
    /// ```
    /// let b = b"(Label)\n@100";
    /// let s = hack_assembler::FirstPass::from_buffer(&b[..])?;
    /// assert_eq!(s.len(), 1);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn from_buffer(
        buffer: impl std::io::BufRead,
    ) -> Result<SymbolTable, hack_interface::Error> {
        let mut fp = Self::new();
        let mut r = Reader::new(buffer);
        for l in r.first_pass() {
            fp.pass_line(l?)?;
        }
        fp.create()
    }

    /// Create a symbol table from first pass lines in memory.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::Assembly;
    /// use hack_assembler::parts::ACommand;
    /// let f = vec![Assembly::Label("Label".to_string()), Assembly::A(ACommand::Address(42))];
    /// let s = hack_assembler::FirstPass::from_slice(&f)?;
    /// assert_eq!(s.len(), 1);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn from_slice(slice: &[Assembly]) -> Result<SymbolTable, hack_interface::Error> {
        let mut fp = Self::new();
        for l in slice {
            fp.pass_line(l.clone().into())?;
        }
        fp.create()
    }

    /// Pass a single line. Once done, call [FirstPass::create] to create the symbol table.
    ///
    /// # Example
    /// ```
    /// use hack_assembler::io::FirstPassLine;
    /// let mut f = hack_assembler::FirstPass::new();
    /// f.pass_line(FirstPassLine::Label("test".to_string()))?;
    /// f.pass_line(FirstPassLine::Command)?;
    /// let s = f.create()?;
    /// assert_eq!(s.len(), 1);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn pass_line(&mut self, line: FirstPassLine) -> Result<(), hack_interface::Error> {
        self.line_count += 1;
        match line {
            FirstPassLine::Empty => Ok(()),
            FirstPassLine::Label(s) => match self.last_label {
                None => {
                    self.last_label = Some(s);
                    Ok(())
                }
                Some(_) => Err(hack_interface::Error::SymbolTable(self.line_count)),
            },
            FirstPassLine::Command => match self.last_label.take() {
                None => {
                    self.command_count += 1;
                    Ok(())
                }
                Some(s) => {
                    self.pass_label(s)?;
                    self.command_count += 1;
                    self.last_label = None;
                    Ok(())
                }
            },
        }
    }

    /// Logic for passing a label.
    fn pass_label(&mut self, label: String) -> Result<(), hack_interface::Error> {
        if ReservedSymbols::is_reserved(&label) {
            Err(hack_interface::Error::SymbolTable(self.line_count))
        } else if let std::collections::hash_map::Entry::Vacant(e) = self.inner.entry(label) {
            e.insert(self.command_count.into());
            Ok(())
        } else {
            Err(hack_interface::Error::SymbolTable(self.line_count))
        }
    }
}

impl Default for FirstPass {
    fn default() -> Self {
        Self::new()
    }
}

pub struct SecondPass<I>
where
    I: std::iter::Iterator<Item = Result<Assembly, hack_interface::Error>>,
{
    iter: I,
    assembler: Assembler,
}

impl<I> SecondPass<I>
where
    I: std::iter::Iterator<Item = Result<Assembly, hack_interface::Error>>,
{
    pub fn new(iter: I, symbol_table: SymbolTable) -> Self {
        Self {
            iter,
            assembler: Assembler::new(symbol_table),
        }
    }
}

impl<I> std::iter::Iterator for SecondPass<I>
where
    I: std::iter::Iterator<Item = Result<Assembly, hack_interface::Error>>,
{
    type Item = Result<hack_interface::Bit16, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        let asml = match self.iter.next() {
            None => return None,
            Some(res_a) => match res_a {
                Ok(a) => a,
                Err(e) => return Some(Err(e)),
            },
        };
        match self.assembler.pass_line(&asml) {
            Some(b) => Some(Ok(b)),
            None => self.next(),
        }
    }
}

pub struct SecondPassTrusted<'a, I>
where
    I: std::iter::Iterator<Item = &'a Assembly>,
{
    iter: I,
    assembler: Assembler,
}

impl<'a, I> SecondPassTrusted<'a, I>
where
    I: std::iter::Iterator<Item = &'a Assembly>,
{
    pub fn new(iter: I, symbol_table: SymbolTable) -> Self {
        Self {
            iter,
            assembler: Assembler::new(symbol_table),
        }
    }
}

impl<'a, I> std::iter::Iterator for SecondPassTrusted<'a, I>
where
    I: std::iter::Iterator<Item = &'a Assembly>,
{
    type Item = hack_interface::Bit16;
    fn next(&mut self) -> Option<Self::Item> {
        let asml = match self.iter.next() {
            None => return None,
            Some(a) => a,
        };
        match self.assembler.pass_line(asml) {
            Some(b) => Some(b),
            None => self.next(),
        }
    }
}
