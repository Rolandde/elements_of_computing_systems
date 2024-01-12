use std::convert::TryFrom;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ReservedSymbols {
    SP,
    LCL,
    ARG,
    THIS,
    THAT,
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    SCREEN,
    KBD,
}

impl ReservedSymbols {
    pub fn is_reserved(symbol: &str) -> bool {
        match Self::try_from(symbol) {
            Ok(_) => true,
            Err(_) => false,
        }
    }
}

impl std::convert::TryFrom<&str> for ReservedSymbols {
    type Error = ();
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "SP" => Ok(ReservedSymbols::SP),
            "LCL" => Ok(ReservedSymbols::LCL),
            "ARG" => Ok(ReservedSymbols::ARG),
            "THIS" => Ok(ReservedSymbols::THIS),
            "THAT" => Ok(ReservedSymbols::THAT),
            "R0" => Ok(ReservedSymbols::R0),
            "R1" => Ok(ReservedSymbols::R1),
            "R2" => Ok(ReservedSymbols::R2),
            "R3" => Ok(ReservedSymbols::R3),
            "R4" => Ok(ReservedSymbols::R4),
            "R5" => Ok(ReservedSymbols::R5),
            "R6" => Ok(ReservedSymbols::R6),
            "R7" => Ok(ReservedSymbols::R7),
            "R8" => Ok(ReservedSymbols::R8),
            "R9" => Ok(ReservedSymbols::R9),
            "R10" => Ok(ReservedSymbols::R10),
            "R11" => Ok(ReservedSymbols::R11),
            "R12" => Ok(ReservedSymbols::R12),
            "R13" => Ok(ReservedSymbols::R13),
            "R14" => Ok(ReservedSymbols::R14),
            "R15" => Ok(ReservedSymbols::R15),
            "SCREEN" => Ok(ReservedSymbols::SCREEN),
            "KBD" => Ok(ReservedSymbols::KBD),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for ReservedSymbols {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            ReservedSymbols::SP => "SP",
            ReservedSymbols::LCL => "LCL",
            ReservedSymbols::ARG => "ARG",
            ReservedSymbols::THIS => "THIS",
            ReservedSymbols::THAT => "THAT",
            ReservedSymbols::R0 => "R0",
            ReservedSymbols::R1 => "R1",
            ReservedSymbols::R2 => "R2",
            ReservedSymbols::R3 => "R3",
            ReservedSymbols::R4 => "R4",
            ReservedSymbols::R5 => "R5",
            ReservedSymbols::R6 => "R6",
            ReservedSymbols::R7 => "R7",
            ReservedSymbols::R8 => "R8",
            ReservedSymbols::R9 => "R9",
            ReservedSymbols::R10 => "R10",
            ReservedSymbols::R11 => "R11",
            ReservedSymbols::R12 => "R12",
            ReservedSymbols::R13 => "R13",
            ReservedSymbols::R14 => "R14",
            ReservedSymbols::R15 => "R15",
            ReservedSymbols::SCREEN => "SCREEN",
            ReservedSymbols::KBD => "KBD",
        };

        write!(f, "{}", s)
    }
}

impl std::convert::From<ReservedSymbols> for hack_interface::Bit15 {
    fn from(value: ReservedSymbols) -> Self {
        match value {
            ReservedSymbols::SP => 0.into(),
            ReservedSymbols::LCL => 1.into(),
            ReservedSymbols::ARG => 2.into(),
            ReservedSymbols::THIS => 3.into(),
            ReservedSymbols::THAT => 4.into(),
            ReservedSymbols::R0 => 0.into(),
            ReservedSymbols::R1 => 1.into(),
            ReservedSymbols::R2 => 2.into(),
            ReservedSymbols::R3 => 3.into(),
            ReservedSymbols::R4 => 4.into(),
            ReservedSymbols::R5 => 5.into(),
            ReservedSymbols::R6 => 6.into(),
            ReservedSymbols::R7 => 7.into(),
            ReservedSymbols::R8 => 8.into(),
            ReservedSymbols::R9 => 9.into(),
            ReservedSymbols::R10 => 10.into(),
            ReservedSymbols::R11 => 11.into(),
            ReservedSymbols::R12 => 12.into(),
            ReservedSymbols::R13 => 13.into(),
            ReservedSymbols::R14 => 14.into(),
            ReservedSymbols::R15 => 15.into(),
            ReservedSymbols::SCREEN => 16385.into(),
            ReservedSymbols::KBD => 24576.into(),
        }
    }
}

impl std::convert::From<ReservedSymbols> for hack_interface::Bit16 {
    fn from(value: ReservedSymbols) -> Self {
        hack_interface::Bit15::from(value).into()
    }
}

/// A parsed A-command can be either an address, a reserved symbol, or a user defined symbol
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ACommand {
    Address(i16),
    Reserved(crate::ReservedSymbols),
    Symbol(String),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CCommand {
    dest: CDest,
    comp: CComp,
    jump: CJump,
}

impl CCommand {
    pub fn new(dest: CDest, comp: CComp, jump: CJump) -> Self {
        CCommand { dest, comp, jump }
    }

    pub fn new_dest(dest: CDest, comp: CComp) -> Self {
        CCommand {
            dest,
            comp,
            jump: CJump::Null,
        }
    }

    pub fn new_jump(comp: CComp, jump: CJump) -> Self {
        CCommand {
            dest: CDest::Null,
            comp,
            jump,
        }
    }
}

impl std::str::FromStr for CCommand {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (destination_str, rest) = match s.split_once("=") {
            Some((d, r)) => (Some(d), r),
            None => (None, s),
        };

        let dest = match destination_str {
            Some(d) => d.parse()?,
            None => CDest::Null,
        };

        let (command_str, jump_str) = match rest.split_once(";") {
            Some((c, j)) => (c, Some(j)),
            None => (rest, None),
        };

        let comp = command_str.parse()?;

        let jump = match jump_str {
            Some(j) => j.parse()?,
            None => CJump::Null,
        };

        Ok(CCommand { dest, comp, jump })
    }
}

impl std::convert::From<CCommand> for hack_interface::Bit16 {
    fn from(value: CCommand) -> Self {
        let dest = <[bool; 3]>::from(value.dest);
        let comp = <[bool; 7]>::from(value.comp);
        let jump = <[bool; 3]>::from(value.jump);

        hack_interface::Bit16::from([
            true, true, true, comp[0], comp[1], comp[2], comp[3], comp[4], comp[5], comp[6],
            dest[0], dest[1], dest[2], jump[0], jump[1], jump[2],
        ])
    }
}

impl std::fmt::Display for CCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let dest_sep = match self.dest {
            CDest::Null => "",
            _ => "=",
        };
        let jump_sep = match self.jump {
            CJump::Null => "",
            _ => ";",
        };
        write!(
            f,
            "{}{dest_sep}{}{jump_sep}{}",
            self.dest, self.comp, self.jump
        )
    }
}

/// The comp part of the C instruction
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CComp {
    Zero,
    One,
    MinumOne,
    D,
    A,
    NotD,
    NotA,
    MinusD,
    MinusA,
    DPlusOne,
    APlusOne,
    DMinusOne,
    AMinusOne,
    DPlusA,
    DMinusA,
    AMinusD,
    DAndA,
    DOrA,
    M,
    NotM,
    MinusM,
    MPlusOne,
    MMinusOne,
    DPlusM,
    DMinusM,
    MMinusD,
    DAndM,
    DOrM,
}

impl CComp {
    /// The first bit of the comp instruction. Is A register a value or a memory address?
    fn a_m_flag(self) -> bool {
        match self {
            CComp::Zero => false,
            CComp::One => false,
            CComp::MinumOne => false,
            CComp::D => false,
            CComp::A => false,
            CComp::NotD => false,
            CComp::NotA => false,
            CComp::MinusD => false,
            CComp::MinusA => false,
            CComp::DPlusOne => false,
            CComp::APlusOne => false,
            CComp::DMinusOne => false,
            CComp::AMinusOne => false,
            CComp::DPlusA => false,
            CComp::DMinusA => false,
            CComp::AMinusD => false,
            CComp::DAndA => false,
            CComp::DOrA => false,
            CComp::M => true,
            CComp::NotM => true,
            CComp::MinusM => true,
            CComp::MPlusOne => true,
            CComp::MMinusOne => true,
            CComp::DPlusM => true,
            CComp::DMinusM => true,
            CComp::MMinusD => true,
            CComp::DAndM => true,
            CComp::DOrM => true,
        }
    }
}

impl std::str::FromStr for CComp {
    type Err = (); // Informative error message happens during parsing

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "0" => Ok(Self::Zero),
            "1" => Ok(Self::One),
            "-1" => Ok(Self::MinumOne),
            "D" => Ok(Self::D),
            "A" => Ok(Self::A),
            "!D" => Ok(Self::NotD),
            "!A" => Ok(Self::NotA),
            "-D" => Ok(Self::MinusD),
            "-A" => Ok(Self::MinusA),
            "D+1" => Ok(Self::DPlusOne),
            "A+1" => Ok(Self::APlusOne),
            "D-1" => Ok(Self::DMinusOne),
            "A-1" => Ok(Self::AMinusOne),
            "D+A" => Ok(Self::DPlusA),
            "D-A" => Ok(Self::DMinusA),
            "A-D" => Ok(Self::AMinusD),
            "D&A" => Ok(Self::DAndA),
            "D|A" => Ok(Self::DOrA),
            "M" => Ok(Self::M),
            "!M" => Ok(Self::NotM),
            "-M" => Ok(Self::MinusM),
            "M+1" => Ok(Self::MPlusOne),
            "M-1" => Ok(Self::MMinusOne),
            "D+M" => Ok(Self::DPlusM),
            "D-M" => Ok(Self::DMinusM),
            "M-D" => Ok(Self::MMinusD),
            "D&M" => Ok(Self::DAndM),
            "D|M" => Ok(Self::DOrM),
            _ => Err(()),
        }
    }
}

impl std::convert::From<CComp> for [bool; 7] {
    fn from(value: CComp) -> Self {
        let c = match value {
            CComp::Zero => hack_kernel::arithmetic::ALU_ZERO,
            CComp::One => hack_kernel::arithmetic::ALU_ONE,
            CComp::MinumOne => hack_kernel::arithmetic::ALU_MINUS_ONE,
            CComp::D => hack_kernel::arithmetic::ALU_X,
            CComp::A | CComp::M => hack_kernel::arithmetic::ALU_Y,
            CComp::NotD => hack_kernel::arithmetic::ALU_X_NOT,
            CComp::NotA | CComp::NotM => hack_kernel::arithmetic::ALU_Y_NOT,
            CComp::MinusD => hack_kernel::arithmetic::ALU_X_MINUS,
            CComp::MinusA | CComp::MinusM => hack_kernel::arithmetic::ALU_Y_MINUS,
            CComp::DPlusOne => hack_kernel::arithmetic::ALU_X_PLUS1,
            CComp::APlusOne | CComp::MPlusOne => hack_kernel::arithmetic::ALU_Y_PLUS1,
            CComp::DMinusOne => hack_kernel::arithmetic::ALU_X_MINUS1,
            CComp::AMinusOne | CComp::MMinusOne => hack_kernel::arithmetic::ALU_Y_MINUS1,
            CComp::DPlusA | CComp::DPlusM => hack_kernel::arithmetic::ALU_X_PLUS_Y,
            CComp::DMinusA | CComp::DMinusM => hack_kernel::arithmetic::ALU_X_MINUS_Y,
            CComp::AMinusD | CComp::MMinusD => hack_kernel::arithmetic::ALU_Y_MINUS_X,
            CComp::DAndA | CComp::DAndM => hack_kernel::arithmetic::ALU_X_AND_Y,
            CComp::DOrA | CComp::DOrM => hack_kernel::arithmetic::ALU_X_OR_Y,
        };

        [value.a_m_flag(), c[0], c[1], c[2], c[3], c[4], c[5]]
    }
}

impl std::fmt::Display for CComp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Zero => "0",
            Self::One => "1",
            Self::MinumOne => "-1",
            Self::D => "D",
            Self::A => "A",
            Self::NotD => "!D",
            Self::NotA => "!A",
            Self::MinusD => "-D",
            Self::MinusA => "-A",
            Self::DPlusOne => "D+1",
            Self::APlusOne => "A+1",
            Self::DMinusOne => "D-1",
            Self::AMinusOne => "A-1",
            Self::DPlusA => "D+A",
            Self::DMinusA => "D-A",
            Self::AMinusD => "A-D",
            Self::DAndA => "D&A",
            Self::DOrA => "D|A",
            Self::M => "M",
            Self::NotM => "!M",
            Self::MinusM => "-M",
            Self::MPlusOne => "M+1",
            Self::MMinusOne => "M-1",
            Self::DPlusM => "D+M",
            Self::DMinusM => "D-M",
            Self::MMinusD => "M-D",
            Self::DAndM => "D&M",
            Self::DOrM => "D|M",
        };
        write!(f, "{}", s)
    }
}

/// The destination part of the C command
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CDest {
    Null,
    M,
    D,
    MD,
    A,
    AM,
    AD,
    AMD,
}

impl std::str::FromStr for CDest {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(CDest::Null),
            "M" => Ok(CDest::M),
            "D" => Ok(CDest::D),
            "MD" => Ok(CDest::MD),
            "A" => Ok(CDest::A),
            "AM" => Ok(CDest::AM),
            "AD" => Ok(CDest::AD),
            "AMD" => Ok(CDest::AMD),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for CDest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CDest::Null => "",
            CDest::M => "M",
            CDest::D => "D",
            CDest::MD => "MD",
            CDest::A => "A",
            CDest::AM => "AM",
            CDest::AD => "AD",
            CDest::AMD => "AMD",
        };
        write!(f, "{}", s)
    }
}

impl std::convert::From<CDest> for [bool; 3] {
    fn from(value: CDest) -> Self {
        match value {
            CDest::Null => [false, false, false],
            CDest::M => [false, false, true],
            CDest::D => [false, true, false],
            CDest::MD => [false, true, true],
            CDest::A => [true, false, false],
            CDest::AM => [true, false, true],
            CDest::AD => [true, true, false],
            CDest::AMD => [true, true, true],
        }
    }
}

/// The jump part of the C command
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CJump {
    Null,
    Greater,
    Equal,
    GreaterEqual,
    Less,
    NotEqual,
    LessEqual,
    Jump,
}

impl std::str::FromStr for CJump {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "" => Ok(CJump::Null),
            "JGT" => Ok(CJump::Greater),
            "JEQ" => Ok(CJump::Equal),
            "JGE" => Ok(CJump::GreaterEqual),
            "JLT" => Ok(CJump::Less),
            "JNE" => Ok(CJump::NotEqual),
            "JLE" => Ok(CJump::LessEqual),
            "JMP" => Ok(CJump::Jump),
            _ => Err(()),
        }
    }
}

impl std::fmt::Display for CJump {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CJump::Null => "",
            CJump::Greater => "JGT",
            CJump::Equal => "JEQ",
            CJump::GreaterEqual => "JGE",
            CJump::Less => "JLT",
            CJump::NotEqual => "JNE",
            CJump::LessEqual => "JLE",
            CJump::Jump => "JMP",
        };
        write!(f, "{}", s)
    }
}

impl std::convert::From<CJump> for [bool; 3] {
    fn from(value: CJump) -> Self {
        match value {
            CJump::Null => [false, false, false],
            CJump::Greater => [false, false, true],
            CJump::Equal => [false, true, false],
            CJump::GreaterEqual => [false, true, true],
            CJump::Less => [true, false, false],
            CJump::NotEqual => [true, false, true],
            CJump::LessEqual => [true, true, false],
            CJump::Jump => [true, true, true],
        }
    }
}
