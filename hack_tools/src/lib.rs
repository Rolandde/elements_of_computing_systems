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
#[derive(Debug, Eq, PartialEq)]
pub struct Bit16 {
    i: [bool; 16],
}

impl std::str::FromStr for Bit16 {
    type Err = Error;
    fn from_str(instruction: &str) -> Result<Self, Self::Err> {
        let mut r = [false; 16];
        if instruction.len() != 16 {
            Err(Error::CharCount(instruction.len()))?
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

/// A big endian 15 bit abstraction for the hack computer.
///
/// Used for memory address.
pub struct Bit15 {
    i: [bool; 15],
}

impl std::str::FromStr for Bit15 {
    type Err = Error;
    fn from_str(instruction: &str) -> Result<Self, Self::Err> {
        let mut r = [false; 15];
        if instruction.len() != 15 {
            Err(Error::CharCount(instruction.len()))?
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
        if i < 0 {panic!("input must be greater than 0")}
        Bit15::from(hack_kernel::from_i15(i))
    }
}

/// Errors during parsing
#[derive(Debug)]
pub enum Error {
    /// Each line is expected to be 16 characters
    CharCount(usize),
    /// Character can either be `0` or `1`. Offset of invalid character is also recorded.
    Char(char, usize),
    /// Upstream IO error
    Io(std::io::Error),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CharCount(i) => write!(f, "expected 16 characters, but got {}", i),
            Self::Char(c, i) => write!(
                f,
                "expected either 0 or 1 character, but got {} at offset {}",
                c, i
            ),
            Self::Io(e) => write!(f, "cannot read: {}", e),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Char(_, _) => None,
            Self::CharCount(_) => None,
            Self::Io(e) => Some(e),
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

pub mod book_exercises;
pub mod string_io;
