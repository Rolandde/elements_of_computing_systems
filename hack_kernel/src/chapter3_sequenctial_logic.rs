//! # Sequential Logic
//!
//! Implementing sequential logic gates from Chapter 3 of the book. The constraint with combinational gates was to use Rust bitwise operators only for the NAND gate. For sequential gates, only DFF keeps state with a Rust primitive type (bool). All other sequential gates keep state with DFF or with gates derived with DFF.
//!
//! ## Note on `None`
//! I tried implementing Dff state as `Option<bool>`. At the beginning of time, no cycles have been run, so there is no state. The problem is that combinational gates only take bool. I could not figure out how to feed `Option<bool>` into combinational gates without using `if`/`match` statements on `Option<bool>` inputs, which is not allowed. Now, can combinational gates be null? In the real world, yes (no electricity), but this code is run on a computer so electricity is given. This means that sequential gates will never be null. Instead, they must be initialized with values.
//!
//! ## Notes on Cycles
//! Sequential gates are controlled by a on (tick, 1) and off (tock, 0) clock. A cycle includes both a tick and a tock. A cycle start can be defined as either when the tick occurs or when the tock occurs. It is at the start of a cycle that sequential gates take their inputs and have valid outputs. At any other time, the output of sequential gates is indeterminate. All sequential gates are activated at the same time. If sequential gates are connected to each other, the inputs they get from each other was set at the start of the previous cycle. This allows a sequential gate to have as input its own output (can't be a direct connection though).
//!
//! ## Note on state getter
//! Initially, there was a `read()` method on each sequential gate that returned the current state of the gate. This was removed as the `cycle()` method itself could always be used to get the current state. I backtracked on that yet again because
//! * `cycle()` method requires `&mut` and it doesn't make sense to expect a gate to be mutable when it's only being read
//! * chapter 5 has a read-only ROM chip that is independent of the clock (has no cycles), so a sequential gate must have a way to access it as a combinational gate
//!
//! The book calls this "probing" a sequential gate. The inputs are set to the desired values and the output is probed. For memory, this means setting the address input and probing for the value output at that address. As the cycle does not happen, the value input and load bit can be indeterminate.

use crate::{arithmetic, gates};

/// The tit-for-tag Data Flip Flop sequential gate
///
/// # Examples
/// ```
/// use hack_kernel::seq_logic::Dff;
/// let mut dff = Dff::new(true);
/// let mut c = dff.cycle(true);
/// assert_eq!(c, true);
/// c = dff.cycle(false);
/// assert_eq!(c, true);
/// c = dff.cycle(false);
/// assert_eq!(c, false);
/// c = dff.cycle(true);
/// assert_eq!(c, false);
/// assert_eq!(dff.probe(), true);
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

    pub fn probe(&self) -> bool {
        self.past_in
    }

    pub fn cycle(&mut self, in_now: bool) -> bool {
        let past = self.past_in;
        self.past_in = in_now;
        past
    }
}

/// The memorable Bit. If `load` is set when cycle starts, the starting cycle will store the input of the previous cycle. Cycle output will be the state from the previous cycle.
///
/// # Examples
/// ```
/// use hack_kernel::seq_logic::Bit;
/// let mut bit = Bit::new(true);
/// let mut c = bit.cycle(false, false);
/// assert_eq!(c, true);
/// c = bit.cycle(false, true);
/// assert_eq!(c, true);
/// c = bit.cycle(false, false);
/// assert_eq!(c, false);
/// assert_eq!(bit.probe(), false);
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

    pub fn probe(&self) -> bool {
        self.state.probe()
    }

    pub fn cycle(&mut self, input: bool, load: bool) -> bool {
        let new = gates::multiplexor_gate(self.probe(), input, load);
        self.state.cycle(new)
    }
}
/// The prodigious Register. Same idea as Bit, except more bits.
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Register};
/// let a = from_i16(22);
/// let b = from_i16(42);
/// let mut reg = Register::new(a);
/// let mut c = reg.cycle(b, false);
/// assert_eq!(c, a);
/// c = reg.cycle(b, true);
/// assert_eq!(c, a);
/// c = reg.cycle(a, false);
/// assert_eq!(c, b);
/// c = reg.cycle(a, true);
/// assert_eq!(c, b);
/// assert_eq!(reg.probe(), a);
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

    pub fn probe(&self) -> [bool; 16] {
        [
            self.state[0].probe(),
            self.state[1].probe(),
            self.state[2].probe(),
            self.state[3].probe(),
            self.state[4].probe(),
            self.state[5].probe(),
            self.state[6].probe(),
            self.state[7].probe(),
            self.state[8].probe(),
            self.state[9].probe(),
            self.state[10].probe(),
            self.state[11].probe(),
            self.state[12].probe(),
            self.state[13].probe(),
            self.state[14].probe(),
            self.state[15].probe(),
        ]
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

/// The proud Ram8
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Ram8};
/// let a = from_i16(22);
/// let address = [true, false, true];
/// let mut ram8 = Ram8::new_0();
/// let mut c = ram8.cycle(address, a, false);
/// assert_eq!(c, from_i16(0));
/// c = ram8.cycle(address, a, true);
/// assert_eq!(c, from_i16(0));
/// c = ram8.cycle(address, from_i16(0), true);
/// assert_eq!(c, a);
/// assert_eq!(ram8.probe(address), from_i16(0));
/// ```
///
pub struct Ram8 {
    state: alloc::vec::Vec<Register>,
}

impl Ram8 {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![
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
            state: alloc::vec![
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

    pub fn probe(&self, address: [bool; 3]) -> [bool; 16] {
        let probe = [
            self.state[0].probe(),
            self.state[1].probe(),
            self.state[2].probe(),
            self.state[3].probe(),
            self.state[4].probe(),
            self.state[5].probe(),
            self.state[6].probe(),
            self.state[7].probe(),
        ];
        gates::multiplexor_8way_16bit_gate(probe, address)
    }

    pub fn cycle(&mut self, address: [bool; 3], input: [bool; 16], load: bool) -> [bool; 16] {
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, address);
        let cycle = [
            self.state[0].cycle(input, load_one_or_none[0]),
            self.state[1].cycle(input, load_one_or_none[1]),
            self.state[2].cycle(input, load_one_or_none[2]),
            self.state[3].cycle(input, load_one_or_none[3]),
            self.state[4].cycle(input, load_one_or_none[4]),
            self.state[5].cycle(input, load_one_or_none[5]),
            self.state[6].cycle(input, load_one_or_none[6]),
            self.state[7].cycle(input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(cycle, address)
    }
}

/// The 120 stars Ram64
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Ram64};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false];
/// let mut ram = Ram64::new_0();
/// let mut c = ram.cycle(address, a, false);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, a, true);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, from_i16(0), true);
/// assert_eq!(c, a);
/// assert_eq!(ram.probe(address), from_i16(0));
/// ```
///
pub struct Ram64 {
    state: alloc::vec::Vec<Ram8>,
}

impl Ram64 {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![
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
            state: alloc::vec![
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

    pub fn probe(&self, address: [bool; 6]) -> [bool; 16] {
        let ram_self_probe = [address[0], address[1], address[2]];
        let ram_8_probe = [address[3], address[4], address[5]];
        let probe = [
            self.state[0].probe(ram_8_probe),
            self.state[1].probe(ram_8_probe),
            self.state[2].probe(ram_8_probe),
            self.state[3].probe(ram_8_probe),
            self.state[4].probe(ram_8_probe),
            self.state[5].probe(ram_8_probe),
            self.state[6].probe(ram_8_probe),
            self.state[7].probe(ram_8_probe),
        ];
        gates::multiplexor_8way_16bit_gate(probe, ram_self_probe)
    }

    pub fn cycle(&mut self, address: [bool; 6], input: [bool; 16], load: bool) -> [bool; 16] {
        let ram_self_add = [address[0], address[1], address[2]];
        let ram_8_add = [address[3], address[4], address[5]];
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, ram_self_add);
        let cycle = [
            self.state[0].cycle(ram_8_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_8_add, input, load_one_or_none[1]),
            self.state[2].cycle(ram_8_add, input, load_one_or_none[2]),
            self.state[3].cycle(ram_8_add, input, load_one_or_none[3]),
            self.state[4].cycle(ram_8_add, input, load_one_or_none[4]),
            self.state[5].cycle(ram_8_add, input, load_one_or_none[5]),
            self.state[6].cycle(ram_8_add, input, load_one_or_none[6]),
            self.state[7].cycle(ram_8_add, input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(cycle, ram_self_add)
    }
}

/// The making it rain Ram512
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Ram512};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true];
/// let mut ram = Ram512::new_0();
/// let mut c = ram.cycle(address, a, false);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, a, true);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, from_i16(0), true);
/// assert_eq!(c, a);
/// assert_eq!(ram.probe(address), from_i16(0));
/// ```
///
pub struct Ram512 {
    state: alloc::vec::Vec<Ram64>,
}

impl Ram512 {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![
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
            state: alloc::vec![
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

    pub fn probe(&self, address: [bool; 9]) -> [bool; 16] {
        let ram_self_probe = [address[0], address[1], address[2]];
        let ram_64_probe = [
            address[3], address[4], address[5], address[6], address[7], address[8],
        ];
        let probe = [
            self.state[0].probe(ram_64_probe),
            self.state[1].probe(ram_64_probe),
            self.state[2].probe(ram_64_probe),
            self.state[3].probe(ram_64_probe),
            self.state[4].probe(ram_64_probe),
            self.state[5].probe(ram_64_probe),
            self.state[6].probe(ram_64_probe),
            self.state[7].probe(ram_64_probe),
        ];
        gates::multiplexor_8way_16bit_gate(probe, ram_self_probe)
    }

    pub fn cycle(&mut self, address: [bool; 9], input: [bool; 16], load: bool) -> [bool; 16] {
        let ram_self_add = [address[0], address[1], address[2]];
        let ram_64_add = [
            address[3], address[4], address[5], address[6], address[7], address[8],
        ];
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, ram_self_add);
        let cycle = [
            self.state[0].cycle(ram_64_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_64_add, input, load_one_or_none[1]),
            self.state[2].cycle(ram_64_add, input, load_one_or_none[2]),
            self.state[3].cycle(ram_64_add, input, load_one_or_none[3]),
            self.state[4].cycle(ram_64_add, input, load_one_or_none[4]),
            self.state[5].cycle(ram_64_add, input, load_one_or_none[5]),
            self.state[6].cycle(ram_64_add, input, load_one_or_none[6]),
            self.state[7].cycle(ram_64_add, input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(cycle, ram_self_add)
    }
}

/// The crystal clear Ram4K
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Ram4K};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true, true, false, false];
/// let mut ram = Ram4K::new_0();
/// let mut c = ram.cycle(address, a, false);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, a, true);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, from_i16(0), true);
/// assert_eq!(c, a);
/// assert_eq!(ram.probe(address), from_i16(0));
/// ```
///
pub struct Ram4K {
    state: alloc::vec::Vec<Ram512>,
}

impl Ram4K {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![
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
            state: alloc::vec![
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

    pub fn probe(&self, address: [bool; 12]) -> [bool; 16] {
        let ram_self_probe = [address[0], address[1], address[2]];
        let ram_512_probe = [
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
        let probe = [
            self.state[0].probe(ram_512_probe),
            self.state[1].probe(ram_512_probe),
            self.state[2].probe(ram_512_probe),
            self.state[3].probe(ram_512_probe),
            self.state[4].probe(ram_512_probe),
            self.state[5].probe(ram_512_probe),
            self.state[6].probe(ram_512_probe),
            self.state[7].probe(ram_512_probe),
        ];
        gates::multiplexor_8way_16bit_gate(probe, ram_self_probe)
    }

    pub fn cycle(&mut self, address: [bool; 12], input: [bool; 16], load: bool) -> [bool; 16] {
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
        let load_one_or_none = gates::demultiplexor_8way_1bit_gate(load, ram_self_add);
        let cycle = [
            self.state[0].cycle(ram_512_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_512_add, input, load_one_or_none[1]),
            self.state[2].cycle(ram_512_add, input, load_one_or_none[2]),
            self.state[3].cycle(ram_512_add, input, load_one_or_none[3]),
            self.state[4].cycle(ram_512_add, input, load_one_or_none[4]),
            self.state[5].cycle(ram_512_add, input, load_one_or_none[5]),
            self.state[6].cycle(ram_512_add, input, load_one_or_none[6]),
            self.state[7].cycle(ram_512_add, input, load_one_or_none[7]),
        ];
        gates::multiplexor_8way_16bit_gate(cycle, ram_self_add)
    }
}

/// The whole universe in Ram16K (unless you initialize two of them)
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Ram16K};
/// let a = from_i16(22);
/// let address = [true, false, true, false, false, false, true, false, true, true, false, false, true, false];
/// let mut ram = Ram16K::new_0();
/// let mut c = ram.cycle(address, a, false);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, a, true);
/// assert_eq!(c, from_i16(0));
/// c = ram.cycle(address, from_i16(0), true);
/// assert_eq!(c, a);
/// assert_eq!(ram.probe(address), from_i16(0));
/// ```
///
pub struct Ram16K {
    state: alloc::vec::Vec<Ram4K>,
}

impl Ram16K {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![
                Ram4K::new_0(),
                Ram4K::new_0(),
                Ram4K::new_0(),
                Ram4K::new_0(),
            ],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: alloc::vec![
                Ram4K::new_1(),
                Ram4K::new_1(),
                Ram4K::new_1(),
                Ram4K::new_1(),
            ],
        }
    }

    pub fn probe(&self, address: [bool; 14]) -> [bool; 16] {
        let ram_self_probe = [address[0], address[1]];
        let ram_4k_probe = [
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
        let probe = [
            self.state[0].probe(ram_4k_probe),
            self.state[1].probe(ram_4k_probe),
            self.state[2].probe(ram_4k_probe),
            self.state[3].probe(ram_4k_probe),
        ];
        gates::multiplexor_4way_16bit_gate(probe, ram_self_probe)
    }

    pub fn cycle(&mut self, address: [bool; 14], input: [bool; 16], load: bool) -> [bool; 16] {
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
        let load_one_or_none = gates::demultiplexor_4way_1bit_gate(load, ram_self_add);
        let cycle = [
            self.state[0].cycle(ram_4k_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_4k_add, input, load_one_or_none[1]),
            self.state[2].cycle(ram_4k_add, input, load_one_or_none[2]),
            self.state[3].cycle(ram_4k_add, input, load_one_or_none[3]),
        ];
        gates::multiplexor_4way_16bit_gate(cycle, ram_self_add)
    }
}

/// The bean-counting Counter. Starts at 0. If in previous cycle:
/// * `inc` is set: next cycle will be one more than previous cycle
/// * `load` is set: will be set as input from previous cycle for next cycle
/// * `reset` is set: will be 0 in next cycle
///
/// # Examples
/// ```
/// use hack_kernel::{from_i16, seq_logic::Counter};
/// let input = from_i16(42);
/// let mut c = Counter::new();
/// let mut n = c.cycle(input, false, false, false);
/// assert_eq!(n, from_i16(0));
/// n = c.cycle(input, true, false, false);
/// assert_eq!(n, from_i16(0));
/// n = c.cycle(input, true, true, false);
/// assert_eq!(n, from_i16(1));
/// n = c.cycle(input, true, false, false);
/// assert_eq!(n, from_i16(42));
/// n = c.cycle(input, true, true, true);
/// assert_eq!(n, from_i16(43));
/// n = c.cycle(input, true, false, false);
/// assert_eq!(n, from_i16(0));
/// assert_eq!(c.probe(), from_i16(1));
/// ```
///
pub struct Counter {
    count: Register,
}

impl Counter {
    pub fn new() -> Self {
        Self {
            count: Register::new_0(),
        }
    }

    pub fn probe(&self) -> [bool; 16] {
        self.count.probe()
    }

    pub fn cycle(&mut self, input: [bool; 16], inc: bool, load: bool, reset: bool) -> [bool; 16] {
        // Not sure if efficient, as it's incremented regardless of the flag
        let mut new =
            gates::multiplexor_multibit_gate(self.probe(), arithmetic::add_one(self.probe()), inc);
        new = gates::multiplexor_multibit_gate(new, input, load);
        new = gates::and_multibit_gate(new, [gates::not_gate(reset); 16]);
        self.count.cycle(new, true)
    }
}

impl Default for Counter {
    fn default() -> Self {
        Self::new()
    }
}
