//! # Sequential Logic
//!
//! Implementing sequential logic gates from Chapter 3 of the book. The constraint with
//! combinational gates was to use Rust bitwise operators only for the NAND gate. For sequential
//! gates, only DFF keeps state with a Rust primitive type (bool). All other sequential gates keep
//! state with DFF or with gates derived with DFF.
//!
//! ## Note on `None`
//! I tried implementing Dff state as `Option<bool>`. At the beginning of time, no cycles have been run, so there is no state.
//! The problem is that combinational gates only take bool. I could not figure out how to feed `Option<bool>` into
//! combinational gates without using `if`/`match` statements on `Option<bool>` inputs, which is not allowed. Now, can combinational gates be null?
//! In the real world, yes (no electricity), but this code is run on a computer so electricity is given. This means that
//! sequential gates will never be null. Instead, they must be initialized with values.
//!
//! ## Notes on Cycles
//! Sequential gates are controlled by a on and off clock. The start of a cycle is propagated to all sequential chips. What is interesting
//! is that input from combinational and sequential gates (even from the gate itself) is allowed at the start of a cycle. In the case of
//! sequential gates, that input was fixed in the previous cycle call. Once the cycle has started, the sequential gate keeps the state
//! derived from the input of the previous cycles.
use crate::{gates, arithmetic};

/// The tit-for-tag Data Flip Flop sequential gate
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::seq_logic::Dff;
/// let mut dff = Dff::new(true);
/// dff.cycle(true);
/// assert_eq!(dff.read(), true);
/// dff.cycle(false);
/// assert_eq!(dff.read(), false);
/// dff.cycle(false);
/// assert_eq!(dff.read(), false);
/// dff.cycle(true);
/// assert_eq!(dff.read(), true);
/// ```
pub struct Dff {
    past_in: bool,
}

impl Dff {
    pub fn new(init: bool) -> Self {
        Dff { past_in: init }
    }

    pub fn new_0() -> Self {
        Dff { past_in: false }
    }

    pub fn new_1() -> Self {
        Dff { past_in: true }
    }

    pub fn cycle(&mut self, in_now: bool) {
        self.past_in = in_now;
    }

    pub fn read(&self) -> bool {
        self.past_in
    }
}

/// The memorable Bit. If `load` is set when cycle starts, the starting cycle will store the input
/// of the previous cycle. If not, starting cycle output will be the output of the previous cycle.
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::seq_logic::Bit;
/// let mut bit = Bit::new(true);
/// bit.cycle(false, false);
/// assert_eq!(bit.read(), true);
/// bit.cycle(false, true);
/// assert_eq!(bit.read(), false);
/// bit.cycle(false, false);
/// assert_eq!(bit.read(), false);
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

    pub fn new_1() -> Self {
        Bit {
            state: Dff::new_1(),
        }
    }

    pub fn read(&self) -> bool {
        self.state.read()
    }

    pub fn cycle(&mut self, input: bool, load: bool) {
        let new = gates::multiplexor_gate(self.read(), input, load);
        self.state.cycle(new);
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
/// reg.cycle(b, false);
/// assert_eq!(reg.read(), a);
/// reg.cycle(b, true);
/// assert_eq!(reg.read(), b);
/// reg.cycle(a, false);
/// assert_eq!(reg.read(), b);
/// reg.cycle(a, true);
/// assert_eq!(reg.read(), a);
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

    pub fn new_0() -> Self {
        Self::new([false; 16])
    }

    pub fn new_1() -> Self {
        Self::new([true; 16])
    }

    pub fn cycle(&mut self, input: [bool; 16], load: bool) {
        self.state[0].cycle(input[0], load);
        self.state[1].cycle(input[1], load);
        self.state[2].cycle(input[2], load);
        self.state[3].cycle(input[3], load);
        self.state[4].cycle(input[4], load);
        self.state[5].cycle(input[5], load);
        self.state[6].cycle(input[6], load);
        self.state[7].cycle(input[7], load);
        self.state[8].cycle(input[8], load);
        self.state[9].cycle(input[9], load);
        self.state[10].cycle(input[10], load);
        self.state[11].cycle(input[11], load);
        self.state[12].cycle(input[12], load);
        self.state[13].cycle(input[13], load);
        self.state[14].cycle(input[14], load);
        self.state[15].cycle(input[15], load);
    }

    pub fn read(&self) -> [bool; 16] {
        [
            self.state[0].read(),
            self.state[1].read(),
            self.state[2].read(),
            self.state[3].read(),
            self.state[4].read(),
            self.state[5].read(),
            self.state[6].read(),
            self.state[7].read(),
            self.state[8].read(),
            self.state[9].read(),
            self.state[10].read(),
            self.state[11].read(),
            self.state[12].read(),
            self.state[13].read(),
            self.state[14].read(),
            self.state[15].read(),
        ]
    }
}

/// The proud Ram8
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Ram8};
/// let a = from_i16(22);
/// let address = [true, false, true];
/// let mut ram8 = Ram8::new_0();
/// assert_eq!(ram8.read(address), from_i16(0));
/// ram8.cycle(address, a, false);
/// assert_eq!(ram8.read(address), from_i16(0));
/// ram8.cycle(address, a, true);
/// assert_eq!(ram8.read(address), a);
/// ```
///
pub struct Ram8 {
    state: [Register; 8],
}

impl Ram8 {
    pub fn new_0() -> Self {
        Self {
            state: [
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
                Register::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: [
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
                Register::new_1(),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 3], input: [bool; 16], load: bool) {
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, address);
        self.state[0].cycle(input, load_one_or_none[0]);
        self.state[1].cycle(input, load_one_or_none[1]);
        self.state[2].cycle(input, load_one_or_none[2]);
        self.state[3].cycle(input, load_one_or_none[3]);
        self.state[4].cycle(input, load_one_or_none[4]);
        self.state[5].cycle(input, load_one_or_none[5]);
        self.state[6].cycle(input, load_one_or_none[6]);
        self.state[7].cycle(input, load_one_or_none[7]);
    }

    pub fn read(&self, address: [bool; 3]) -> [bool; 16] {
        let bool_state = [
            self.state[0].read(),
            self.state[1].read(),
            self.state[2].read(),
            self.state[3].read(),
            self.state[4].read(),
            self.state[5].read(),
            self.state[6].read(),
            self.state[7].read(),
        ];
        gates::multiplexor_8way_16bit_gate(bool_state, address)
    }
}

/// The I'm not the worst Ram64
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Ram64};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false];
/// let mut ram = Ram64::new_0();
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, false);
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, true);
/// assert_eq!(ram.read(address), a);
/// ```
///
pub struct Ram64 {
    state: [Ram8; 8],
}

impl Ram64 {
    pub fn new_0() -> Self {
        Self {
            state: [
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
                Ram8::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: [
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
                Ram8::new_1(),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 6], input: [bool; 16], load: bool) {
        let load_one_or_none =
            gates::demultiplexor_8way_1bit_gate(load, [address[0], address[1], address[2]]);
        let ram_8_add = [address[3], address[4], address[5]];
        self.state[0].cycle(ram_8_add, input, load_one_or_none[0]);
        self.state[1].cycle(ram_8_add, input, load_one_or_none[1]);
        self.state[2].cycle(ram_8_add, input, load_one_or_none[2]);
        self.state[3].cycle(ram_8_add, input, load_one_or_none[3]);
        self.state[4].cycle(ram_8_add, input, load_one_or_none[4]);
        self.state[5].cycle(ram_8_add, input, load_one_or_none[5]);
        self.state[6].cycle(ram_8_add, input, load_one_or_none[6]);
        self.state[7].cycle(ram_8_add, input, load_one_or_none[7]);
    }

    pub fn read(&self, address: [bool; 6]) -> [bool; 16] {
        let ram_self_add = [address[0], address[1], address[2]];
        let ram_8_add = [address[3], address[4], address[5]];
        let bool_state = [
            self.state[0].read(ram_8_add),
            self.state[1].read(ram_8_add),
            self.state[2].read(ram_8_add),
            self.state[3].read(ram_8_add),
            self.state[4].read(ram_8_add),
            self.state[5].read(ram_8_add),
            self.state[6].read(ram_8_add),
            self.state[7].read(ram_8_add),
        ];
        gates::multiplexor_8way_16bit_gate(bool_state, ram_self_add)
    }
}

/// The making it rain Ram512
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Ram512};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true];
/// let mut ram = Ram512::new_0();
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, false);
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, true);
/// assert_eq!(ram.read(address), a);
/// ```
///
pub struct Ram512 {
    state: [Ram64; 8],
}

impl Ram512 {
    pub fn new_0() -> Self {
        Self {
            state: [
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
                Ram64::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: [
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
                Ram64::new_1(),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 9], input: [bool; 16], load: bool) {
        let load_one_or_none =
            gates::demultiplexor_8way_1bit_gate(load, [address[0], address[1], address[2]]);
        let ram_64_add = [
            address[3], address[4], address[5], address[6], address[7], address[8],
        ];
        self.state[0].cycle(ram_64_add, input, load_one_or_none[0]);
        self.state[1].cycle(ram_64_add, input, load_one_or_none[1]);
        self.state[2].cycle(ram_64_add, input, load_one_or_none[2]);
        self.state[3].cycle(ram_64_add, input, load_one_or_none[3]);
        self.state[4].cycle(ram_64_add, input, load_one_or_none[4]);
        self.state[5].cycle(ram_64_add, input, load_one_or_none[5]);
        self.state[6].cycle(ram_64_add, input, load_one_or_none[6]);
        self.state[7].cycle(ram_64_add, input, load_one_or_none[7]);
    }

    pub fn read(&self, address: [bool; 9]) -> [bool; 16] {
        let ram_self_add = [address[0], address[1], address[2]];
        let ram_64_add = [
            address[3], address[4], address[5], address[6], address[7], address[8],
        ];
        let bool_state = [
            self.state[0].read(ram_64_add),
            self.state[1].read(ram_64_add),
            self.state[2].read(ram_64_add),
            self.state[3].read(ram_64_add),
            self.state[4].read(ram_64_add),
            self.state[5].read(ram_64_add),
            self.state[6].read(ram_64_add),
            self.state[7].read(ram_64_add),
        ];
        gates::multiplexor_8way_16bit_gate(bool_state, ram_self_add)
    }
}

/// The crystal clear Ram4K
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Ram4K};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true, true, false, false];
/// let mut ram = Ram4K::new_0();
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, false);
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, true);
/// assert_eq!(ram.read(address), a);
/// ```
///
pub struct Ram4K {
    state: [Ram512; 8],
}

impl Ram4K {
    pub fn new_0() -> Self {
        Self {
            state: [
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
                Ram512::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: [
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
                Ram512::new_1(),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 12], input: [bool; 16], load: bool) {
        let load_one_or_none =
            gates::demultiplexor_8way_1bit_gate(load, [address[0], address[1], address[2]]);
        let ram_512_add = [
            address[3],
            address[4],
            address[5],
            address[6],
            address[7],
            address[8],
            address[9],
            address[10],
            address[11],
        ];
        self.state[0].cycle(ram_512_add, input, load_one_or_none[0]);
        self.state[1].cycle(ram_512_add, input, load_one_or_none[1]);
        self.state[2].cycle(ram_512_add, input, load_one_or_none[2]);
        self.state[3].cycle(ram_512_add, input, load_one_or_none[3]);
        self.state[4].cycle(ram_512_add, input, load_one_or_none[4]);
        self.state[5].cycle(ram_512_add, input, load_one_or_none[5]);
        self.state[6].cycle(ram_512_add, input, load_one_or_none[6]);
        self.state[7].cycle(ram_512_add, input, load_one_or_none[7]);
    }

    pub fn read(&self, address: [bool; 12]) -> [bool; 16] {
        let ram_self_add = [address[0], address[1], address[2]];
        let ram_512_add = [
            address[3],
            address[4],
            address[5],
            address[6],
            address[7],
            address[8],
            address[9],
            address[10],
            address[11],
        ];
        let bool_state = [
            self.state[0].read(ram_512_add),
            self.state[1].read(ram_512_add),
            self.state[2].read(ram_512_add),
            self.state[3].read(ram_512_add),
            self.state[4].read(ram_512_add),
            self.state[5].read(ram_512_add),
            self.state[6].read(ram_512_add),
            self.state[7].read(ram_512_add),
        ];
        gates::multiplexor_8way_16bit_gate(bool_state, ram_self_add)
    }
}

/// The whole universe in Ram16K (unless you initialize two of them)
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Ram16K};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true, true, false, false, true, false];
/// let mut ram = Ram16K::new_0();
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, false);
/// assert_eq!(ram.read(address), from_i16(0));
/// ram.cycle(address, a, true);
/// assert_eq!(ram.read(address), a);
/// ```
///
pub struct Ram16K {
    state: [Ram4K; 4],
}

impl Ram16K {
    pub fn new_0() -> Self {
        Self {
            state: [
                Ram4K::new_0(),
                Ram4K::new_0(),
                Ram4K::new_0(),
                Ram4K::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: [
                Ram4K::new_1(),
                Ram4K::new_1(),
                Ram4K::new_0(),
                Ram4K::new_0(),
            ],
        }
    }

    pub fn cycle(&mut self, address: [bool; 14], input: [bool; 16], load: bool) {
        let load_one_or_none = gates::demultiplexor_4way_1bit_gate(load, [address[0], address[1]]);
        let ram_4k_add = [
            address[2],
            address[3],
            address[4],
            address[5],
            address[6],
            address[7],
            address[8],
            address[9],
            address[10],
            address[11],
            address[12],
            address[13],
        ];
        self.state[0].cycle(ram_4k_add, input, load_one_or_none[0]);
        self.state[1].cycle(ram_4k_add, input, load_one_or_none[1]);
        self.state[2].cycle(ram_4k_add, input, load_one_or_none[2]);
        self.state[3].cycle(ram_4k_add, input, load_one_or_none[3]);
    }

    pub fn read(&self, address: [bool; 14]) -> [bool; 16] {
        let ram_self_add = [address[0], address[1]];
        let ram_4k_add = [
            address[2],
            address[3],
            address[4],
            address[5],
            address[6],
            address[7],
            address[8],
            address[9],
            address[10],
            address[11],
            address[12],
            address[13],
        ];
        let bool_state = [
            self.state[0].read(ram_4k_add),
            self.state[1].read(ram_4k_add),
            self.state[2].read(ram_4k_add),
            self.state[3].read(ram_4k_add),
        ];
        gates::multiplexor_4way_16bit_gate(bool_state, ram_self_add)
    }
}

/// The bean-counting Counter. Starts at 0. If in previous cycle:
/// * `reset` is set: will be 0 in next cycle
/// * `load` is set: will be set as input from previous cycle for next cycle
/// * `inc` is set: next cycle will be one more than previous cycle
/// 
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, seq_logic::Counter};
/// let input = from_i16(42);
/// let mut c = Counter::new();
/// assert_eq!(c.read(), from_i16(0));
/// c.cycle(input, false, false, false);
/// assert_eq!(c.read(), from_i16(0));
/// c.cycle(input, true, false, false);
/// assert_eq!(c.read(), from_i16(1));
/// c.cycle(input, true, true, false);
/// assert_eq!(c.read(), input);
/// c.cycle(input, true, false, false);
/// assert_eq!(c.read(), from_i16(43));
/// c.cycle(input, true, true, true);
/// assert_eq!(c.read(), from_i16(0));
/// ```
/// 
pub struct Counter {
    count: Register
}

impl Counter {
    pub fn new() -> Self {
        Self{count: Register::new_0()}
    }
    
    pub fn cycle(&mut self, input: [bool; 16], inc: bool, load: bool, reset: bool) {
        let state = self.read();
        // Not sure if efficient, as it's incremented regardless of the flag
        let mut new = gates::multiplexor_multibit_gate(state, arithmetic::add_one(state), inc);
        new = gates::multiplexor_multibit_gate(new, input, load);
        new = gates::and_multibit_gate(new, [gates::not_gate(reset); 16]);
        self.count.cycle(new, true)

    }

    pub fn read(&self) -> [bool; 16] {
        self.count.read()
    }
}