//! Tools for interacting with the [hack kernel][hack_kernel].
//!
//! [Bit16] is the entrypoint used by all upstream abstractions.

/// A 16 bit abstraction for the hack computer.
///
/// # Examples
/// ```
/// use hack_interface::{Bit16, Error};
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

/// A 15 bit abstraction for the hack computer.
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

/// Write to a ROM from any type that can be cast into [crate::Bit16].
///
/// # Example
/// ```
/// use hack_interface::{Bit16, RomWriter};
/// use hack_kernel::Computer;
/// use std::str::FromStr;
/// let mut rw = RomWriter::new();
/// rw.write_instruction(42);
/// rw.write_instruction("0110001111001010".parse::<Bit16>().unwrap());
/// let mut c = Computer::new(rw.create_rom());
/// c.cycle(false);
/// ```
pub struct RomWriter {
    inner: hack_kernel::Rom32KWriter,
}

impl RomWriter {
    pub fn new() -> Self {
        Self {
            inner: hack_kernel::Rom32KWriter::new(),
        }
    }

    pub fn write_instruction(&mut self, instruction: impl Into<crate::Bit16>) {
        self.inner.write_next(instruction.into().i)
    }

    pub fn create_rom(self) -> hack_kernel::Rom32K {
        self.inner.create_rom()
    }
}

/// Create a ROM from a buffer that holds instructions in `.hack` format
///
/// # Examples
/// ```
/// use hack_interface::write_rom_from_buffer;
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
    let mut writer = RomWriter::new();
    let mut reader = crate::hack_io::Reader::new(buf);
    for (i, instruction) in reader.instructions().enumerate() {
        let inst = instruction.unwrap_or_else(|e| panic!("Failed on line {}: {}", i + 1, e));
        writer.write_instruction(inst);
    }
    writer.create_rom()
}

/// Create a ROM from a `.hack` file
///
/// # Examples
/// ```
/// use hack_interface::write_rom_from_file;
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

pub mod hack_io;

#[cfg(test)]
mod cpu_tests {
    use super::*;

    #[test]
    fn count_screen_pixels() {
        let input = b"";
        let rom = write_rom_from_buffer(&input[..]);
        let c = hack_kernel::Computer::new(rom);
        let scan = Scan::new(&c);
        let pixel_count = scan.collect::<Vec<bool>>().len();
        assert_eq!(pixel_count, 131072);
    }
}

#[cfg(test)]
mod book_tests {
    use super::*;

    /// Machine code to add 2 and 3 and store result to RAM\[0\].
    pub const TWO_PLUS_THREE: &'static str = "0000000000000010
1110110000010000
0000000000000011
1110000010010000
0000000000000000
1110001100001000
";

    /// Add 2 and 3 and store result to RAM\[0\].
    ///
    /// The hack machine code was given to test that the computer functions properly.
    #[test]
    pub fn chapter5_add() {
        let rom = write_rom_from_buffer(TWO_PLUS_THREE.as_bytes());
        let mut computer = hack_kernel::Computer::new(rom);
        for _ in 0..6 {
            computer.cycle(false);
        }
        let add = Debugger::new(&mut computer).read_memory("000000000000000".parse().unwrap());
        assert_eq!(add, "0000000000000101".parse().unwrap());
    }

    /// Write the max number to RAM\[2\], with the two input numbers at RAM\[0\] and RAM\[1\]
    ///
    /// The hack machine code was given to test that the computer functions properly.
    pub fn chapter5_max(a: Bit16, b: Bit16) -> Bit16 {
        let rom = write_rom_from_buffer(PICK_MAX.as_bytes());
        let mut computer = hack_kernel::Computer::new(rom);
        let mut debugger = Debugger::new(&mut computer);
        debugger.write_memory(Bit15::from(0), a);
        debugger.write_memory(Bit15::from(1), b);
        // Machine code loops infinitely from the last line
        while debugger.read_cpu_counter() != Bit16::from(15) {
            debugger.computer().cycle(false)
        }
        debugger.read_memory(Bit15::from(2))
    }

    /// Machine code to Write the max number to RAM\[2\], with the two input numbers at RAM\[0\] and RAM\[1\]
    pub const PICK_MAX: &'static str = "0000000000000000
1111110000010000
0000000000000001
1111010011010000
0000000000001010
1110001100000001
0000000000000001
1111110000010000
0000000000001100
1110101010000111
0000000000000000
1111110000010000
0000000000000010
1110001100001000
0000000000001110
1110101010000111
";

    #[test]
    pub fn chapter5_max_test() {
        assert_eq!(chapter5_max(1.into(), 2.into()), 2.into());
        assert_eq!(chapter5_max(2.into(), 1.into()), 2.into());
        assert_eq!(chapter5_max(0.into(), 0.into()), 0.into());
        assert_eq!(
            chapter5_max(Bit16::from(-1), Bit16::from(-2)),
            Bit16::from(-1)
        );
    }
}
