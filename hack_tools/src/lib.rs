/// A single instruction in the hack machine language
///
/// # Examples
/// ```
/// use hack_tools::{Instruction, Error};
/// let mut i: Result<Instruction, Error> = "0110001111001010".parse();
/// assert!(i.is_ok());
/// // Instructions are exactly 16 characters long
/// i = "01100011110010100".parse();
/// assert!(i.is_err());
/// // Instructions only consist of 0s and 1s
/// i = "0110001111001012".parse();
/// assert!(i.is_err());
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct Instruction {
    i: [bool; 16],
}

impl std::str::FromStr for Instruction {
    type Err= Error;
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
        Ok(Instruction { i: r })
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
    Io(std::io::Error)
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
            Self::Io(e) => write!(f, "cannot read: {}", e)
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

pub mod string_io;