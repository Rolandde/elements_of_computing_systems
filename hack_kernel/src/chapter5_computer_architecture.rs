//! # Computer Architecture
//!
//! Putting it all together to create the hardware of a [Computer] (Chapter 5 of the book). Chapter 4 describes the machine language instructions that the CPU needs to support.
//!
//! The [CPU] was fun to write as the book showed a very good hint diagram on how all the sequential gates click together. The flags of the [ALU][crate::arithmetic::alu] match the instruction set of the CPU, reducing the problem to just dealing with updating the registers correctly and figuring out which instruction to jump to next.
//!
//! The computer's [memory][DataMemory] supports standard data write and read, but also holds the memory representation of the screen and keyboard. The computer provides a [screen][Computer::screen] and a [keyboard][Computer::update_key] memory map that allow the mysterious outside world to interact with the computer. The implementation of the memory wasn't any different from the sequential gates seen in Chapter 3. One thing that took some thinking was that the memory is 32K, but not all of it is used by the CPU. My instinct was to add a panic in case that does happen, but decided to let it happen and pay in debugging time later.
//!
//! Once the [Computer] is created, it has very limited interfaces. It can be cycled (run the next instruction), look at the screen data map, or set the currently pressed key. A [Debugger] can be attached to the computer to expose all the internal states of the computer.

use crate::arithmetic;
use crate::gates;
use crate::seq_logic::{Counter, Ram16K, Register};

/// Convenience container for CPU outputs.
///
/// I could have used a tuple for purity, but having names is a lot easier.
pub struct CPUOutput {
    /// Value to write to M
    pub out_m: [bool; 16],
    /// Should you write to M
    pub write_m: bool,
    /// The address of M (where the value needs to be written to)
    pub address_m: [bool; 15],
    /// The address of the next instruction
    pub pc: [bool; 15],
}

/// The almighty CPU.
///
/// See [Self::cycle()] for input parameters and [CPUOutput] for outputs.
///
/// # Examples
/// ```
/// use hack_kernel::architecture::CPU;
/// let mut cpu = CPU::new();
/// let mut inst = [
///     false,  // Set A register to 10
///     false, false, false, false, false, false, false, false, false, false, false, true, false, true, false
/// ];
/// let mut out = cpu.cycle([false; 16], inst, false);  // M is dummy input as its not used
/// assert_eq!(out.write_m, false);
///
/// inst = [
///     true, true, true, false,  // C instruction that operates on value of A
///     true, true, false, false, true, true,  // Computation gets -A
///     false, true, false,  // D register is set to computation
///     false, false, false,  // No jump     
/// ];
/// out = cpu.cycle([false; 16], inst, false);
/// assert_eq!(out.write_m, false);
///
/// inst = [
///     true, true, true, false,  // C instruction that operates on value of A
///     false, false, false, true, true, true,  // Computation gets A-D: 10 - (-10)
///     false, false, true,  // M register is set to computation
///     false, false, false,  // No jump     
/// ];
/// out = cpu.cycle([false; 16], inst, false);
/// assert_eq!(out.write_m, true);
/// assert_eq!(out.out_m, [false, false, false, false, false, false, false, false, false, false, false, true, false, true, false, false])
/// ```
pub struct CPU {
    reg_d: Register,
    reg_a: Register,
    counter: Counter,
}

impl CPU {
    /// Sets registers and counters to all 0s.
    pub fn new() -> Self {
        Self {
            reg_d: Register::new_0(),
            reg_a: Register::new_0(),
            counter: Counter::new(),
        }
    }

    /// Run one cycle of the CPU
    ///
    /// Arguments:
    /// * `in_m`: Value of M (content of RAM\[A]\)
    /// * `instruction`: Machine instruction to execute
    /// * `reset`: If true, [CPUOutput::pc] will be set to 0. The program will go back to the beginning, regardless of instruction given.
    ///
    pub fn cycle(&mut self, in_m: [bool; 16], instruction: [bool; 16], reset: bool) -> CPUOutput {
        // true if C instruction, otherwise A
        let c_instr = instruction[0];
        // true if using M register value, otherwise A value
        let m_bit = instruction[3];
        let c_bits = [
            instruction[4],
            instruction[5],
            instruction[6],
            instruction[7],
            instruction[8],
            instruction[9],
        ];
        // puts the ALU calculation to A reg (first bit), D reg (second bit), or M (third bit)
        // If third bit is set, writeM is set to true and outM is the value to write to M
        let d_bits = [instruction[10], instruction[11], instruction[12]];
        // Jump if alu calculation is less than 0 (first bit true), equal to 0 (second bit true),
        // or greater than 0 (third bit true). Notice that if all bits are true, jump will happen.
        let j_bits = [instruction[13], instruction[14], instruction[15]];

        let mut reg_a = self.reg_a.probe();
        let reg_d = self.reg_d.probe();
        // The a bit determines if we are using value of A register or the value of the address it points to
        let alu_y = gates::multiplexor_multibit_gate(reg_a, in_m, m_bit);

        let (calc, equal_0, less_0) = arithmetic::alu(reg_d, alu_y, c_bits);
        let greater_0 = gates::not_gate(gates::or_gate(equal_0, less_0));

        self.reg_a.cycle(
            gates::multiplexor_multibit_gate(instruction, calc, c_instr),
            // Write to A register if A instruction or if C instruction and destination bit set for A register
            gates::or_gate(
                gates::not_gate(c_instr),
                gates::and_gate(c_instr, d_bits[0]),
            ),
        );
        // A instruction will never write to D register
        self.reg_d.cycle(calc, gates::and_gate(c_instr, d_bits[1]));

        reg_a = self.reg_a.probe();

        let mut jump = gates::and_gate(j_bits[0], less_0);
        jump = gates::or_gate(jump, gates::and_gate(j_bits[1], equal_0));
        jump = gates::or_gate(jump, gates::and_gate(j_bits[2], greater_0));
        // No jumping if it's an A instruction
        jump = gates::and_gate(c_instr, jump);

        // Increase by default, but load will override. Reset will override all.
        self.counter.cycle(reg_a, true, jump, reset);
        // Read the current counter state (dummy input as it worn't be set)
        let next = self.counter.probe();

        // The first bit acts as the control bit and is not part of the address
        // The address is of the A register now rather than at the beginning of the cycle
        // The previous version was buggy, storing `reg_a` before the cycle and then using it here. The CPU doesn't have anywhere to store it!!!
        let address_m = [
            reg_a[1], reg_a[2], reg_a[3], reg_a[4], reg_a[5], reg_a[6], reg_a[7], reg_a[8],
            reg_a[9], reg_a[10], reg_a[11], reg_a[12], reg_a[13], reg_a[14], reg_a[15],
        ];

        let pc = [
            next[1], next[2], next[3], next[4], next[5], next[6], next[7], next[8], next[9],
            next[10], next[11], next[12], next[13], next[14], next[15],
        ];

        // A instruction never writes to M
        let write_m = gates::and_gate(c_instr, d_bits[2]);

        CPUOutput {
            out_m: calc,
            write_m,
            address_m,
            pc,
        }
    }
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
    }
}

/// The gamer Rom32K
///
/// This gate is read only, so once initialized there is no way to modify it. [Rom32KWriter] is used to create a ROM.
///
pub struct Rom32K {
    state: CheatingDataMemory,
}

impl Rom32K {
    pub fn read(&self, address: [bool; 15]) -> [bool; 16] {
        self.state.probe(address)
    }
}

/// The mysterious writer of Rom32K
///
/// [Rom32K] cannot be written to, which makes creating it difficult. Think of this as a machine that comes with an empty Rom32K chip (all 0s). While the Rom chip is attached to the writer, you can write to it. Once you remove it, the writer disgorges the Rom chip, which now and forever is read-only.
///
pub struct Rom32KWriter {
    state: CheatingDataMemory,
    pos: [bool; 16],
}

impl Rom32KWriter {
    pub fn new() -> Self {
        Self {
            state: CheatingDataMemory::new_0(),
            pos: [false; 16],
        }
    }

    pub fn write_next(&mut self, input: [bool; 16]) {
        self.state.cycle(to_15_bit(self.pos), input, true);
        self.pos = arithmetic::add_one(self.pos);
    }

    pub fn create_rom(self) -> Rom32K {
        Rom32K { state: self.state }
    }
}

impl Default for Rom32KWriter {
    fn default() -> Self {
        Self::new()
    }
}

/// The very very slow DataMemory, holding the RAM, Screen memory map, and Keyboard memory map.
///
/// It takes >10s to scan through the screen memory map, so not used in [Computer]. See [crate] intro for details.
pub struct DataMemory {
    state: alloc::vec::Vec<Ram16K>,
}

impl DataMemory {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![Ram16K::new_0(), Ram16K::new_0()],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: alloc::vec![Ram16K::new_1(), Ram16K::new_1()],
        }
    }

    pub fn probe(&self, address: [bool; 15]) -> [bool; 16] {
        let ram_self_probe = address[0];
        let ram_16k_probe = [
            address[1],
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
            address[14],
        ];
        let probe = [
            self.state[0].probe(ram_16k_probe),
            self.state[1].probe(ram_16k_probe),
        ];
        gates::multiplexor_multibit_gate(probe[0], probe[1], ram_self_probe)
    }

    pub fn cycle(&mut self, address: [bool; 15], input: [bool; 16], load: bool) -> [bool; 16] {
        let ram_self_add = address[0];
        let ram_16k_add = [
            address[1],
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
            address[14],
        ];
        let load_one_or_none = gates::demultiplexor_gate(load, ram_self_add);
        let cycle = [
            self.state[0].cycle(ram_16k_add, input, load_one_or_none[0]),
            self.state[1].cycle(ram_16k_add, input, load_one_or_none[1]),
        ];
        gates::multiplexor_multibit_gate(cycle[0], cycle[1], ram_self_add)
    }
}

/// The on-steroids memory. Used instead of [DataMemory].
///
/// It's fast because it breaks the rules of the game. See [crate] into for details.
pub struct CheatingDataMemory {
    state: alloc::vec::Vec<[bool; 16]>,
}

impl CheatingDataMemory {
    pub fn new_0() -> Self {
        Self {
            state: alloc::vec![[false; 16]; 32768],
        }
    }

    pub fn new_1() -> Self {
        Self {
            state: alloc::vec![[true; 16]; 32768],
        }
    }

    fn address_to_index(address: [bool; 15]) -> usize {
        address.iter().enumerate().fold(0_usize, |acc, (i, b)| {
            if *b {
                let exp = (14 - i) as u32;
                acc + usize::pow(2_usize, exp)
            } else {
                acc
            }
        })
    }

    pub fn probe(&self, address: [bool; 15]) -> [bool; 16] {
        self.state[Self::address_to_index(address)]
    }

    pub fn cycle(&mut self, address: [bool; 15], input: [bool; 16], load: bool) -> [bool; 16] {
        let i = Self::address_to_index(address);
        let current_val = self.state[i];
        if load {
            self.state[i] = input;
        }
        current_val
    }
}

/// The final Hack computer.
///
/// # Examples
/// ```
/// use hack_kernel::architecture::{Computer, Rom32KWriter};
/// let rom = Rom32KWriter::new().create_rom();
/// let mut computer = Computer::new(rom);
/// // Run the first instruction
/// computer.cycle(false);
/// ```
pub struct Computer {
    data_memory: CheatingDataMemory,
    rom: Rom32K,
    cpu: CPU,
}

impl Computer {
    /// The ROM chip (that holds the instructions) needs to be given to the computer.
    ///
    /// Think of this as inserting the game cartridge before turning the computer on.
    pub fn new(rom: Rom32K) -> Self {
        Self {
            data_memory: CheatingDataMemory::new_0(),
            rom,
            cpu: CPU::new(),
        }
    }

    /// The screen of the computer.
    pub fn screen(&self, address: [bool; 13]) -> [bool; 16] {
        // The address space for the screen is constant and reserved for it only
        let screen_addrs = [
            true,
            false,
            address[0],
            address[1],
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
        ];
        self.data_memory.probe(screen_addrs)
    }

    /// Let the computer know which key is currently being pressed. If no key is pressed, this is set to 0.
    pub fn update_key(&mut self, key: [bool; 16]) {
        let key_addrs = [
            true, true, false, false, false, false, false, false, false, false, false, false,
            false, false, false,
        ];
        self.data_memory.cycle(key_addrs, key, true);
    }

    /// Run one CPU cycle
    ///
    /// If reset is set, the CPU will go back to instruction 0 for the next cycle
    pub fn cycle(&mut self, reset: bool) {
        let next_instr = self.cpu.counter.probe();
        let instr = self.rom.read(to_15_bit(next_instr));
        let m_addrs = self.cpu.reg_a.probe();
        let m_value = self.data_memory.probe(to_15_bit(m_addrs));

        let out = self.cpu.cycle(m_value, instr, reset);
        self.data_memory
            .cycle(out.address_m, out.out_m, out.write_m);
    }
}

/// Memory is 16 bit, but most memory address space is 15 bit. This avoids annoying typing.
fn to_15_bit(i: [bool; 16]) -> [bool; 15] {
    [
        i[1], i[2], i[3], i[4], i[5], i[6], i[7], i[8], i[9], i[10], i[11], i[12], i[13], i[14],
        i[15],
    ]
}

/// Look inside the [Computer]
pub struct Debugger<'a> {
    computer: &'a mut Computer,
}

impl<'a> Debugger<'a> {
    pub fn new(computer: &'a mut Computer) -> Self {
        Self { computer }
    }

    /// Access to the public [Computer] interface
    ///
    /// # Examples
    /// ```
    /// use hack_kernel::architecture::{Computer, Debugger, Rom32KWriter};
    /// let rom = Rom32KWriter::new().create_rom();
    /// let mut computer = Computer::new(rom);
    /// let mut debugger = Debugger::new(&mut computer);
    /// debugger.computer().cycle(false);
    /// ```
    pub fn computer(&mut self) -> &mut Computer {
        self.computer
    }

    pub fn read_cpu_counter(&self) -> [bool; 16] {
        self.computer.cpu.counter.probe()
    }

    pub fn read_cpu_register_a(&self) -> [bool; 16] {
        self.computer.cpu.reg_a.probe()
    }

    pub fn read_cpu_register_d(&self) -> [bool; 16] {
        self.computer.cpu.reg_d.probe()
    }

    pub fn read_memory(&self, address: [bool; 15]) -> [bool; 16] {
        self.computer.data_memory.probe(address)
    }

    pub fn read_rom(&self, address: [bool; 15]) -> [bool; 16] {
        self.computer.rom.read(address)
    }

    pub fn write_memory(&mut self, address: [bool; 15], input: [bool; 16]) {
        self.computer.data_memory.cycle(address, input, true);
    }

    pub fn write_register_a(&mut self, input: [bool; 16]) {
        self.computer.cpu.reg_a.cycle(input, true);
    }

    pub fn write_register_d(&mut self, input: [bool; 16]) {
        self.computer.cpu.reg_d.cycle(input, true);
    }
}

#[cfg(test)]
mod cpu_tests {
    use super::*;
    use crate::from_i16;

    #[test]
    fn set_a_reg() {
        let mut cpu = CPU::new();
        assert_eq!(cpu.reg_a.cycle([false; 16], false), from_i16(0));
        let inst = [
            false, // Set A register to 10
            false, false, false, false, false, false, false, false, false, false, false, true,
            false, true, false,
        ];
        let out = cpu.cycle([false; 16], inst, false); // M is dummy input as its not used
        assert_eq!(cpu.reg_a.cycle([false; 16], false), from_i16(10));
        assert_eq!(out.write_m, false);
        assert_eq!(out.pc, to_15_bit(from_i16(1)));
    }

    #[test]
    fn test_destinations() {
        let mut cpu = CPU::new();
        // Positive number will start with 0 and be an instruction to set the A register to that
        cpu.cycle([false; 16], from_i16(9876), false);
        let inst = [
            true, true, true, false, // C instruction that operates on value of A
            true, true, false, false, true, true, // Computation gets -A
            true, true, true, // Set new value to all
            false, false, false, // No jump
        ];
        let out = cpu.cycle([false; 16], inst, false);
        assert_eq!(cpu.reg_a.cycle([false; 16], false), from_i16(-9876));
        assert_eq!(cpu.reg_d.cycle([false; 16], false), from_i16(-9876));
        assert_eq!(out.write_m, true);
        assert_eq!(out.out_m, from_i16(-9876));
        assert_eq!(out.address_m, to_15_bit(from_i16(-9876)));
        assert_eq!(out.pc, to_15_bit(from_i16(2)));
    }

    #[test]
    fn test_jumps_and_reset() {
        let mut cpu = CPU::new();
        let mut inst = [
            false, // Set A register to 10
            false, false, false, false, false, false, false, false, false, false, false, true,
            false, true, false,
        ];
        cpu.cycle([false; 16], inst, false);
        inst = [
            true, true, true, false, // C instruction
            true, true, false, false, false, false, // Computation gets A
            false, false, false, // Don't assign to anything
            true, true, false, // Jump if less than or equal to 0 (so no jump)
        ];
        let mut out = cpu.cycle([false; 16], inst, false);
        assert_eq!(out.pc, to_15_bit(from_i16(2)));

        inst = [
            true, true, true, false, // C instruction
            true, true, false, false, false, false, // Computation gets A
            false, false, false, // Don't assign to anything
            false, false, true, // Jump as A is greater than 0 (jumps to whatever is in A)
        ];
        out = cpu.cycle([false; 16], inst, false);
        assert_eq!(out.pc, to_15_bit(from_i16(10)));

        //Jump to 10 again, but this time reset is set, so should be 0
        out = cpu.cycle([false; 16], inst, true);
        assert_eq!(out.pc, to_15_bit(from_i16(0)));
    }

    #[test]
    fn test_jump_greater_than_0() {
        // Test that jump does not happen if jump is set to greater than 0 and computation is 0
        let mut cpu = CPU::new();
        let mut inst = [
            false, // Set A register to 10
            false, false, false, false, false, false, false, false, false, false, false, true,
            false, true, false,
        ];
        cpu.cycle([false; 16], inst, false);

        inst = [
            true, true, true, false, // C instruction
            true, false, true, false, true, false, // Computation yields 0
            false, false, false, // Don't assign to anything
            false, false, true, // Jump as A is greater than 0 (no jump)
        ];
        let out = cpu.cycle([false; 16], inst, false);
        assert_eq!(out.pc, to_15_bit(from_i16(2)));
    }

    #[test]
    /// Initially, memory was held in arrays, which caused stack overflows (memory reached 4MB).
    ///
    /// This test makes no assert statements and just checks for a stack overflow panic.
    fn test_stack_overflow() {
        let _x = DataMemory::new_0();
    }
}
