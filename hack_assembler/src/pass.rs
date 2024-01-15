//! Logic for doing first and second pass.

use crate::io::{AssemblyLines, FirstPassLine, Reader};
use crate::parts::{ACommand, ReservedSymbols};
use crate::Assembly;

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
        use std::convert::TryFrom;
        match ReservedSymbols::try_from(k) {
            Ok(b) => Some(b.into()),
            Err(_) => self.inner.get(k).copied(),
        }
    }
}

/// Go through assembly and generate a [SymbolTable] that holds the labels.
pub struct FirstPass {
    inner: std::collections::HashMap<String, hack_interface::Bit15>,
    last_label: Option<String>,
    line_count: i16,
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
    /// use hack_assembler::io::FirstPassLine;
    /// let f = vec![FirstPassLine::Label("Label".to_string()), FirstPassLine::Command];
    /// let s = hack_assembler::FirstPass::from_slice(&f)?;
    /// assert_eq!(s.len(), 1);
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn from_slice(slice: &[FirstPassLine]) -> Result<SymbolTable, hack_interface::Error> {
        let mut fp = Self::new();
        for l in slice {
            fp.pass_line(l.clone())?;
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
                    self.pass_label(s, self.command_count)?;
                    self.command_count += 1;
                    self.last_label = None;
                    Ok(())
                }
            },
        }
    }

    /// Logic for passing a label.
    fn pass_label(&mut self, label: String, line: i16) -> Result<(), hack_interface::Error> {
        if ReservedSymbols::is_reserved(&label) {
            Err(hack_interface::Error::SymbolTable(line))
        } else if self.inner.contains_key(&label) {
            Err(hack_interface::Error::SymbolTable(line))
        } else {
            self.inner.insert(label, line.into());
            Ok(())
        }
    }
}

/// An iterator that spits out the binary .hack format from assembly.
///
/// [SymbolTable] must be created by [FirstPass] if labels are in the assembly file.
pub struct SecondPass<'a, R> {
    inner: AssemblyIter<'a, R>,
    symbol_table: SymbolTable,
    variable_symbol_count: i16,
    line_count: i16,
}

impl<'a, R: std::io::BufRead> SecondPass<'a, R> {
    /// Do second pass from parsed assembly in memory.
    ///
    /// # Examples
    /// ```
    /// use hack_assembler::{Assembly, SecondPass, SymbolTable};
    /// let i = vec![Assembly::A(42.into())];
    /// let iter = SecondPass::new_from_slice(&i, SymbolTable::empty());
    /// # Ok::<(), hack_interface::Error>(())
    /// ```
    pub fn new_from_slice(slice: &'a [Assembly], symbol_table: SymbolTable) -> Self {
        Self {
            inner: AssemblyIter::Slice(slice.into_iter()),
            symbol_table,
            variable_symbol_count: 16,
            line_count: 0,
        }
    }

    /// Do a second pass from a buffer.
    pub fn new_from_buffer(buffer: R, symbol_table: SymbolTable) -> Self {
        Self {
            inner: AssemblyIter::Buffer(Reader::new(buffer).assembly_lines()),
            symbol_table,
            variable_symbol_count: 16,
            line_count: 0,
        }
    }

    fn assemble_a_command(
        &mut self,
        a: ACommand,
    ) -> Result<hack_interface::Bit16, hack_interface::Error> {
        match a {
            ACommand::Address(b) => Ok(b.into()),
            ACommand::Reserved(r) => Ok(r.into()),
            ACommand::Symbol(s) => match self.symbol_table.inner.get(&s) {
                Some(b) => Ok(hack_interface::Bit16::from(*b)),
                None => {
                    let current_address = self.variable_symbol_count.into();
                    self.symbol_table.inner.insert(s, current_address);
                    self.variable_symbol_count += 1;
                    Ok(current_address.into())
                }
            },
        }
    }
}

impl<'a, R: std::io::BufRead> std::iter::Iterator for SecondPass<'a, R> {
    type Item = Result<hack_interface::Bit16, hack_interface::Error>;
    fn next(&mut self) -> Option<Self::Item> {
        self.line_count += 1;
        let line = match self.inner.next() {
            None => return None,
            Some(res) => match res {
                Ok(l) => l,
                Err(e) => return Some(Err(e)),
            },
        }
        .into_owned();

        match line {
            Assembly::Empty => self.next(),
            Assembly::A(a_cmd) => Some(self.assemble_a_command(a_cmd)),
            Assembly::C(c_cmd) => Some(Ok(c_cmd.into())),
            Assembly::Label(_) => self.next(),
        }
    }
}

/// Iterator that can hold iterators from buffer or from memory
enum AssemblyIter<'a, R> {
    Buffer(AssemblyLines<R>),
    Slice(std::slice::Iter<'a, Assembly>),
}

impl<'a, R: std::io::BufRead> AssemblyIter<'a, R> {
    fn next(&mut self) -> Option<Result<std::borrow::Cow<Assembly>, hack_interface::Error>> {
        match self {
            Self::Buffer(a) => match a.next() {
                None => None,
                Some(l) => match l {
                    Ok(assml) => Some(Ok(std::borrow::Cow::Owned(assml))),
                    Err(e) => Some(Err(e)),
                },
            },
            Self::Slice(a) => match a.next() {
                None => None,
                Some(l) => Some(Ok(std::borrow::Cow::Borrowed(l))),
            },
        }
    }
}

#[cfg(test)]
mod assembly_pass_tests {
    use super::*;
    use crate::{Assembly, SecondPass, SymbolTable};
    #[test]
    fn test_second_pass() -> Result<(), hack_interface::Error> {
        let i = vec![Assembly::A(42.into())];
        let iter: SecondPass<'_, &[u8]> = SecondPass::new_from_slice(&i, SymbolTable::empty());
        Ok(())
    }
}
