/// Errors during VM functioning
#[derive(Debug)]
pub enum Error {
    /// The command has too few, too many, or wrong type of arguments
    InvalidArgs(u16),
    /// Upstream IO error.
    Io(std::io::Error),
    /// The command is not part of the VM spec
    UnknownCommand(u16),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidArgs(line) => write!(f, "wrong number or type or arguments on line {}", line),
            Self::Io(e) => write!(f, "cannot read: {}", e),
            Self::UnknownCommand(line) => write!(f, "unknown command on line {}", line),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::InvalidArgs(_) => None,
            Self::Io(e) => Some(e),
            Self::UnknownCommand(_) => None,
        }
    }
}

impl std::convert::From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

pub mod reader;