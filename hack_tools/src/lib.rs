//! Tools for interacting with the [hack kernel][hack_kernel]

/// A big endian 16 bit abstraction for the hack computer.
///
/// # Examples
/// ```
/// use hack_tools::{Bit16, Error};
/// let mut i: Result<Bit16, Error> = "0110001111001010".parse();
/// assert!(i.is_ok());
/// // 16 bits are exactly 16 characters long
/// i = "01100011110010100".parse();
/// assert!(i.is_err());
/// // Bits only consist of 0s and 1s
/// i = "0110001111001012".parse();
/// assert!(i.is_err());
/// ```
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct Bit16 {
    i: [bool; 16],
}

impl std::str::FromStr for Bit16 {
    type Err = Error;
    fn from_str(instruction: &str) -> Result<Self, Self::Err> {
        let mut r = [false; 16];
        if instruction.len() != 16 {
            Err(Error::CharCount(16))?
        }
        for (i, c) in instruction.chars().enumerate() {
            match c {
                '0' => Ok(()),
                '1' => {
                    r[i] = true;
                    Ok(())
                }
                _ => Err(Error::Char(c, i)),
            }?;
        }
        Ok(Bit16 { i: r })
    }
}

impl std::convert::From<[bool; 16]> for Bit16 {
    fn from(i: [bool; 16]) -> Self {
        Bit16 { i }
    }
}

impl std::convert::From<i16> for Bit16 {
    fn from(i: i16) -> Self {
        Bit16::from(hack_kernel::from_i16(i))
    }
}

impl std::convert::From<Bit15> for Bit16 {
    fn from(b: Bit15) -> Self {
        Bit16 {
            i: [
                false, b.i[0], b.i[1], b.i[2], b.i[3], b.i[4], b.i[5], b.i[6], b.i[7], b.i[8],
                b.i[9], b.i[10], b.i[11], b.i[12], b.i[13], b.i[14],
            ],
        }
    }
}

impl std::fmt::Display for Bit16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let x: String = self.i.iter().map(|&b| if b { '1' } else { '0' }).collect();
        write!(f, "{}", x)
    }
}

/// A big endian 15 bit abstraction for the hack computer.
///
/// Used for memory address.
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub struct Bit15 {
    i: [bool; 15],
}

impl std::str::FromStr for Bit15 {
    type Err = Error;
    fn from_str(instruction: &str) -> Result<Self, Self::Err> {
        let mut r = [false; 15];
        if instruction.len() != 15 {
            Err(Error::CharCount(15))?
        }
        for (i, c) in instruction.chars().enumerate() {
            match c {
                '0' => Ok(()),
                '1' => {
                    r[i] = true;
                    Ok(())
                }
                _ => Err(Error::Char(c, i)),
            }?;
        }
        Ok(Bit15 { i: r })
    }
}

impl std::convert::From<[bool; 15]> for Bit15 {
    fn from(i: [bool; 15]) -> Self {
        Bit15 { i }
    }
}

impl std::convert::From<i16> for Bit15 {
    fn from(i: i16) -> Self {
        if i < 0 {
            panic!("input must be greater than 0")
        }
        Bit15::from(hack_kernel::from_i15(i))
    }
}

impl std::fmt::Display for Bit15 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let x: String = self.i.iter().map(|&b| if b { '1' } else { '0' }).collect();
        write!(f, "{}", x)
    }
}

/// Errors during parsing
#[derive(Debug)]
pub enum Error {
    /// An A-command is expected to begin with an `@` character and be an address or valid symbol.
    ACommand(i16),
    /// One more characters between `(` and `)` followed by a command
    AssemblyLabel(i16),
    /// The C-command is dest=comp;jump, with dest and jump being optional
    CCommand(i16),
    /// String input is the wrong length, with expected length specified.
    CharCount(usize),
    /// Character can either be `0` or `1`. Offset of invalid character is also recorded.
    Char(char, usize),
    /// Upstream IO error.
    Io(std::io::Error),
    /// Duplicated symbol
    SymbolTable(i16),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ACommand(line) => write!(f, "invalid a-command on line {}", line),
            Self::AssemblyLabel(line) => write!(f, "invalid label on line {}", line),
            Self::CCommand(line) => write!(f, "invalid c-command on line {}", line),
            Self::CharCount(i) => write!(f, "input must be {} character(s)", i),
            Self::Char(c, i) => write!(
                f,
                "expected either 0 or 1 character, but got {} at offset {}",
                c, i
            ),
            Self::Io(e) => write!(f, "cannot read: {}", e),
            Self::SymbolTable(line) => write!(f, "duplicated symbol on line {}", line),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ACommand(_) => None,
            Self::AssemblyLabel(_) => None,
            Self::CCommand(_) => None,
            Self::Char(_, _) => None,
            Self::CharCount(_) => None,
            Self::Io(e) => Some(e),
            Self::SymbolTable(_) => None,
        }
    }
}

impl std::convert::From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

/// Look at the internals of the [hack_kernel::Computer]
pub struct Debugger<'a> {
    debug: hack_kernel::Debugger<'a>,
}

impl<'a> Debugger<'a> {
    pub fn new(computer: &'a mut hack_kernel::Computer) -> Self {
        Self {
            debug: hack_kernel::Debugger::new(computer),
        }
    }

    pub fn computer(&mut self) -> &mut hack_kernel::Computer {
        self.debug.computer()
    }

    pub fn read_cpu_counter(&self) -> Bit16 {
        Bit16::from(self.debug.read_cpu_counter())
    }

    pub fn read_cpu_register_a(&self) -> Bit16 {
        Bit16::from(self.debug.read_cpu_register_a())
    }

    pub fn read_cpu_register_d(&self) -> Bit16 {
        Bit16::from(self.debug.read_cpu_register_d())
    }

    pub fn read_memory(&self, address: Bit15) -> Bit16 {
        Bit16::from(self.debug.read_memory(address.i))
    }

    pub fn write_memory(&mut self, address: Bit15, input: Bit16) {
        self.debug.write_memory(address.i, input.i)
    }
}

/// An iterator over the screen of the computer.
///
/// Starts at top left and goes left to right. (Like reading a book)
pub struct Scan<'a> {
    computer: &'a hack_kernel::Computer,
    current_address: i16,
    current_memory: std::vec::IntoIter<bool>,
}

impl<'a> Scan<'a> {
    pub fn new(computer: &'a hack_kernel::Computer) -> Self {
        let screen = computer.screen(Self::to_13bit(0)).to_vec();
        Self {
            computer,
            current_address: 0,
            current_memory: screen.into_iter(),
        }
    }

    /// Only positive numbers (first bit is 0, and then ignore the next two bits)
    fn to_13bit(i: i16) -> [bool; 13] {
        let bit_15 = hack_kernel::from_i15(i);
        [
            bit_15[2], bit_15[3], bit_15[4], bit_15[5], bit_15[6], bit_15[7], bit_15[8], bit_15[9],
            bit_15[10], bit_15[11], bit_15[12], bit_15[13], bit_15[14],
        ]
    }
}

impl<'a> std::iter::Iterator for Scan<'a> {
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        match self.current_memory.next() {
            Some(b) => Some(b),
            None => {
                self.current_address += 1;
                if self.current_address < 8192 {
                    self.current_memory = self
                        .computer
                        .screen(Self::to_13bit(self.current_address))
                        .to_vec()
                        .into_iter();
                    self.current_memory.next()
                } else {
                    None
                }
            }
        }
    }
}

pub mod assembly;
pub mod assembly_io;
pub mod book_exercises;
pub mod hack_io;

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn count_screen_pixels() {
        let input = b"";
        let rom = hack_io::write_rom_from_buffer(&input[..]);
        let c = hack_kernel::Computer::new(rom);
        let scan = Scan::new(&c);
        let pixel_count = scan.collect::<Vec<bool>>().len();
        assert_eq!(pixel_count, 131072);
    }
}
