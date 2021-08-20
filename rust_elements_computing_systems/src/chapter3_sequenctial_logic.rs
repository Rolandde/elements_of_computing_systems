//! # Sequential Logic
//!
//! Implementing sequential logic gates from Chapter 3 of the book. The constraint with
//! combinational gates was to use Rust bitwise operators only for the NAND gate. For sequential
//! gates, only DFF keeps state with a Rust primitive type (bool). All other sequential gates keep
//! state with DFF or with gates derived with DFF.
//!
//! ## Note on cheating with `Copy` and `Clone`
//! Should you be allowed to copy a sequential gate. No, in the sense that your largest sequential gate
//! is the whole universe, so how do you copy a universe. Yes, in the sense that 1 + 1 = 2 and if there is
//! enough space for one universe there should be space for two universes.
//! 
//! Now for the real reason. If I want to write a large array using `[T; 1234567890]` expression, T must implement
//! the `Copy` trait. I could have written it out manually [true, true, . . . . ], but no. I tried implementing Copy
//! manually, but what am I trying to prove. Then I had the insight that `Copy` trait is not required, as I can build
//! bigger gates by chaining smaller gates together.

use core::panic;

use crate::gates;

/// The tit-for-tag Data Flip Flop sequential gate
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::seq_logic::Dff;
/// let mut dff = Dff::new(true);  // in(t=0) = true; out(t=0) = in(t=-1) = None
/// assert_eq!(dff.cycle(true), true);  // in(t=1) = true; out(t=1) = in(t=0) = true
/// assert_eq!(dff.read(), true);
/// assert_eq!(dff.cycle(false), true); // in(t=2) = false; out(t=2) = in(t=1) = true
/// assert_eq!(dff.read(), false);
/// assert_eq!(dff.cycle(false), false);
/// assert_eq!(dff.cycle(true), false);
/// assert_eq!(dff.cycle(true), true);
/// ```
pub struct Dff {
    past_in: bool,
}

impl Dff {
    pub fn new(init: bool) -> Self {
        Dff { past_in: init }
    }

    pub fn new_0() -> Self {
        Dff {past_in: false}
    }

    pub fn cycle(&mut self, in_now: bool) -> bool {
        let past = self.past_in;
        self.past_in = in_now;
        past
    }

    pub fn read(&self) -> bool {
        self.past_in
    }
}

/// The tit-for-tag Data Flip Flop sequential gate
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::seq_logic::Dff;
/// let mut dff = Dff2::new(true);  // in(t=0) = true; out(t=0) = in(t=-1) = None
/// assert_eq!(dff.cycle(true), true);  // in(t=1) = true; out(t=1) = in(t=0) = true
/// assert_eq!(dff.read(), true);
/// assert_eq!(dff.cycle(false), true); // in(t=2) = false; out(t=2) = in(t=1) = true
/// assert_eq!(dff.read(), false);
/// assert_eq!(dff.cycle(false), false);
/// assert_eq!(dff.cycle(true), false);
/// assert_eq!(dff.cycle(true), true);
/// ```
pub struct Dff2 {
    past_in: Option<bool>,
}

impl Dff2 {
    pub fn new() -> Self {
        Dff2 { past_in: None }
    }

    pub fn cycle(&mut self, in_now: bool) {
        let past = self.past_in;
        self.past_in = Some(in_now);
    }

    pub fn read(&self) -> bool {
        match self.past_in {
            Some(b) => b,
            None => panic!("no time, no memory")
        }
    }
}

impl AsRef<bool> for Dff {
    fn as_ref(&self) -> &bool {
        &self.past_in
    }
}

/// The memorable Bit. If `load` was set in previous cycle, next cycle call will be the input
/// of the previous cycle. If not, current cycle output will be the output of the previous cycle.
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::seq_logic::Bit;
/// let mut bit = Bit::new(true);
/// assert_eq!(bit.cycle(false, false), true);
/// assert_eq!(bit.cycle(false, false), true);
/// assert_eq!(bit.cycle(false, true), true);
/// assert_eq!(bit.cycle(true, true), false);
/// assert_eq!(bit.cycle(true, false), true);
/// ```
///
pub struct Bit {
    state: Dff,
}

impl Bit {
    pub fn new(init: bool) -> Self {
        Bit {
            state: Dff::new(init),
        }
    }

    pub fn new_0() -> Self {
        Bit {
            state: Dff::new_0(),
        }
    }

    pub fn cycle(&mut self, input: bool, load: bool) -> bool {
        let new = gates::multiplexor_gate(self.state.past_in, input, load);
        self.state.cycle(new)
    }
}

/// The prodigious Register. Same idea as Bit, except more bits.
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Register};
/// let a = from_i16(22);
/// let b = from_i16(42);
/// let mut reg = Register::new(a);
/// assert_eq!(reg.cycle(b, false), a);
/// assert_eq!(reg.cycle(b, true), a);
/// assert_eq!(reg.cycle(b, true), b);
/// assert_eq!(reg.cycle(a, false), b);
/// assert_eq!(reg.cycle(a, true), b);
/// assert_eq!(reg.cycle(a, true), a);
/// ```
///
pub struct Register {
    state: [Bit; 16],
}

impl Register {
    pub fn new(init: [bool; 16]) -> Self {
        Register {
            state: [
                Bit::new(init[0]),
                Bit::new(init[1]),
                Bit::new(init[2]),
                Bit::new(init[3]),
                Bit::new(init[4]),
                Bit::new(init[5]),
                Bit::new(init[6]),
                Bit::new(init[7]),
                Bit::new(init[8]),
                Bit::new(init[9]),
                Bit::new(init[10]),
                Bit::new(init[11]),
                Bit::new(init[12]),
                Bit::new(init[13]),
                Bit::new(init[14]),
                Bit::new(init[15]),
            ],
        }
    }

    pub fn cycle(&mut self, input: [bool; 16], load: bool) -> [bool; 16] {
        [
            self.state[0].cycle(input[0], load),
            self.state[1].cycle(input[1], load),
            self.state[2].cycle(input[2], load),
            self.state[3].cycle(input[3], load),
            self.state[4].cycle(input[4], load),
            self.state[5].cycle(input[5], load),
            self.state[6].cycle(input[6], load),
            self.state[7].cycle(input[7], load),
            self.state[8].cycle(input[8], load),
            self.state[9].cycle(input[9], load),
            self.state[10].cycle(input[10], load),
            self.state[11].cycle(input[11], load),
            self.state[12].cycle(input[12], load),
            self.state[13].cycle(input[13], load),
            self.state[14].cycle(input[14], load),
            self.state[15].cycle(input[15], load),
        ]
    }
}

pub struct Ram8 {
    state: [Register; 8],
}

impl Ram8 {
    pub fn new(init: [bool; 16]) -> Self {
        Ram8 {
            state: [
                Register::new(init),
                Register::new(init),
                Register::new(init),
                Register::new(init),
                Register::new(init),
                Register::new(init),
                Register::new(init),
                Register::new(init),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 3], input: [bool; 16], load: bool) -> [bool; 16] {
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, address);
        let new_state = [
            self.state[0].cycle(input, load_one_or_none[0]),
            self.state[1].cycle(input, load_one_or_none[1]),
            self.state[2].cycle(input, load_one_or_none[2]),
            self.state[3].cycle(input, load_one_or_none[3]),
            self.state[4].cycle(input, load_one_or_none[4]),
            self.state[5].cycle(input, load_one_or_none[5]),
            self.state[6].cycle(input, load_one_or_none[6]),
            self.state[7].cycle(input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(new_state, address)

        
    }
}

pub struct Ram64 {
    state: [Ram8; 8]
}

impl Ram64 {
    pub fn cycle(&mut self, address: [bool; 6], input: [bool; 16], load: bool) -> [bool; 16] {
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, [address[0], address[1], address[2]]);
        let ram_8_add = [address[3], address[4], address[5]];
        let new_state = [
            self.state[0].cycle(ram_8_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_8_add, input, load_one_or_none[1]),
            self.state[2].cycle(ram_8_add, input, load_one_or_none[2]),
            self.state[3].cycle(ram_8_add, input, load_one_or_none[3]),
            self.state[4].cycle(ram_8_add, input, load_one_or_none[4]),
            self.state[5].cycle(ram_8_add, input, load_one_or_none[5]),
            self.state[6].cycle(ram_8_add, input, load_one_or_none[6]),
            self.state[7].cycle(ram_8_add, input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(new_state, ram_8_add)
    }
}

/*
impl SequentialChip for RegisterOneBit {
    type In = [bool; 2];
    type Out = bool;

    fn new() -> Self {
        RegisterOneBit {state: Dff::new(), past_in: None, past_load: None}
    }

    fn state(&self) -> Option<Self::In> {
        match (self.past_in, self.past_load) {
            (None, None) => None,
            (Some(i), Some(l)) => Some([i, l]),
            _ => panic!("impossible state")
        }
    }

    fn tick_tock(&mut self, in_now: Self::In) -> Option<Self::Out> {
        if let(Some([i, l])) = self.state() {

        } else {
            None
        }
    }
}
*/

/*
/// Tit-for-tat DFF
pub struct FlipFlop {
    inc_past: bool,
    load_past: bool,
    reset_past: bool,
    in_past: Option<[bool; 16]>,
    out_past: Option<[bool; 16]>,
}

impl FlipFlop {
    pub fn new() -> Self {
        FlipFlop {inc_past: false, load_past: false, reset_past: false, in_past: None, out_past: None}
    }

    pub fn tick_tock(&mut self, in_now: [bool; 16], inc: bool, load: bool, reset: bool) -> Option<[bool; 16]> {
        let out_now = if self.reset_past {
            Some([false; 16])
        } else if self.load_past {
            self.in_past
        } else if self.inc_past {
            match self.out_past {
                None => panic!("cannot increment of first cycle"),
                Some(b16) => Some(arithmetic::add_one(b16))
            }
        } else {
            self.out_past
        };

        self.inc_past = inc;
        self.load_past = load;
        self.reset_past = reset;
        self.in_past = Some(in_now);
        self.out_past = out_now;

        out_now
    }
}
*/
