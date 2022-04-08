//! # Gate Implementation
//!
//! Implementing gates using only `NAND` (Not And) and any gates derived using `NAND` (Section 1.3).
//! As `NAND` is magically given, the Rust bitwise operations are used to construct the gate. All other
//! gates did not use any Rust logic at all (assignment were used for code readability). The gates were
//! implemented in order given in the book, which made puzzling them out easier.
//! 
//! ## Notes on using `bool` for 0 (`false`) and 1 (`true`)
//! `bool` works, but `[bool; 8]` takes up 8 times as much space as `u8` if I understand 
//! [how much space types need](https://doc.rust-lang.org/core/mem/fn.size_of.html). I tried making u8
//! work and the compiler would not let me. So this is why I like [bool; N]. Other reasons include:
//! 
//! * It's intuitive. A primitive type than can be in only two states. 
//! * Length is explicit. `bool`, `[bool; 4]`, `[bool; 8]` cannot be directly compared
//!
//! ## NOT Gate
//! If the first input of the NAND gate is `true`, then the second value will be flipped.
//!
//! ## AND Gate
//! NOT(NAND)
//!
//! ## OR Gate
//! This was the first tricky one. Noticing that `OR(false, false)` is the only false one and linking that
//! to `NAND(false, false)` being the only true one gave the solution
//!
//! ## XOR Gate
//! Looked for two gates that with 0 bit on opposite ends and 1 bit otherwise.
//!
//! ## Multiplexor
//! Many false starts, most of which were due to it being late. The big step towards the solution was thinking
//! that column 1 and 2 below could give a solution(did not know how to make those columns). The intuitive jump
//! was that the bit the selector hid should be set to 0. Once those columns were written down, it was easy to
//! see how to construct them with previous gates.
//!
//! | AND(b, sel) | AND(a, NOT(sel) | OR |
//! |-------------|-----------------|----|
//! | 0           | 0               | 0  |
//! | 0           | 0               | 0  |
//! | 0           | 1               | 1  |
//! | 0           | 1               | 1  |
//! | 0           | 0               | 0  |
//! | 1           | 0               | 1  |
//! | 0           | 0               | 0  |
//! | 1           | 0               | 1  |
//!
//! ## Demultiplexor gate
//! First one with two outputs. Multiplexor was used to select the right position in the output.
//!
//! ## Multi-bit gates (NOT, AND, OR, MULTIPLEXOR)
//! Boring, especially since I couldn't even cheat and use iterators to construct the array outputs
//!
//! ## Multi-way OR gate
//! The hint is "think forks". I took this to mean OR gates feeding into OR gates. Even if a single `true`
//! is present, it will propagate through all subsequent gates.
//!
//! ## 4-way 16-bit Multiplexor gate
//! The selector is two bits. It was intuitive how the two bits can be with multi-big Multiplexor to select the
//! right output
//!
//! ## 8-way 16-bit Multiplexor gate
//! Same logic as the 4-way Multiplexor
//!
//! ## 4-way 1-bit Demultiplexor gate
//! This one required an unexpectedly complex complement of gates. The idea is to find gate combinations that
//! are one bit for one selector and the other bit for the other three selectors. For 00, that would be OR
//! (false for 00, true for all others). Demultiplexors can then be used to slot the input bit into the right
//! position.
//!
//! ## 8-way 1-bit Demultiplexor gate
//! This was done differently that the 4-way gate. Rather than use a Multiplexor and tediously construct eight
//! unique flags that place the input flag in the right position, two 4-way Demultiplexors were used. The trick
//! in that approach was to use the first selector bit to turn off the input bit for the appropriate
//! 4-way Demultiplexor.

/// The Not And gate. The only gate that is implemented with Rust bitwise operators.
/// All other gate logic will use only other gates.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::nand_gate;
/// assert_eq!(nand_gate(false, false), true);
/// assert_eq!(nand_gate(true, false), true);
/// assert_eq!(nand_gate(false, true), true);
/// assert_eq!(nand_gate(true, true), false);
/// ```
///
pub fn nand_gate(a: bool, b: bool) -> bool {
    !(a & b)
}

/// The beloved And gate.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::and_gate;
/// assert_eq!(and_gate(false, false), false);
/// assert_eq!(and_gate(true, false), false);
/// assert_eq!(and_gate(false, true), false);
/// assert_eq!(and_gate(true, true), true);
/// ```
///
pub fn and_gate(a: bool, b: bool) -> bool {
    not_gate(nand_gate(a, b))
}

/// The can-do-it-all Multi-Bit And gate. Does AND operation on each position.
/// # Examples
///
/// ```
/// use hack_kernel::gates::and_multibit_gate;
/// assert_eq!(
///     and_multibit_gate(
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
///     ),
///     [true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false]
/// )
pub fn and_multibit_gate(a: [bool; 16], b: [bool; 16]) -> [bool; 16] {
    [
        and_gate(a[0], b[0]),
        and_gate(a[1], b[1]),
        and_gate(a[2], b[2]),
        and_gate(a[3], b[3]),
        and_gate(a[4], b[4]),
        and_gate(a[5], b[5]),
        and_gate(a[6], b[6]),
        and_gate(a[7], b[7]),
        and_gate(a[8], b[8]),
        and_gate(a[9], b[9]),
        and_gate(a[10], b[10]),
        and_gate(a[11], b[11]),
        and_gate(a[12], b[12]),
        and_gate(a[13], b[13]),
        and_gate(a[14], b[14]),
        and_gate(a[15], b[15]),
    ]
}

/// The divisive Demultiplexor gate. For output, if selector=0 then [input, 0] else [0, input]. 
/// In words, put input in first or second position of output given the selector.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::demultiplexor_gate;
/// assert_eq!(demultiplexor_gate(false, false), [false, false]);
/// assert_eq!(demultiplexor_gate(true, false), [true, false]);
/// assert_eq!(demultiplexor_gate(false, true), [false, false]);
/// assert_eq!(demultiplexor_gate(true, true), [false, true]);
/// ```
///
pub fn demultiplexor_gate(a: bool, sel: bool) -> [bool; 2] {
    [
        multiplexor_gate(a, false, sel),
        multiplexor_gate(false, a, sel),
    ]
}

/// The quartering 4-Way 1-Bit Demultiplexor gate. Output is 4 bits, with input in
/// first position if selector is 00, second position for 01, third position for 10,
/// fourth position for 11. Unselected positions are always 0.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::demultiplexor_4way_1bit_gate;
/// assert_eq!(demultiplexor_4way_1bit_gate(false, [false, false]), [false, false, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(false, [false, true]), [false, false, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(false, [true, false]), [false, false, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(false, [true, true]), [false, false, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(true, [false, false]), [true, false, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(true, [false, true]), [false, true, false, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(true, [true, false]), [false, false, true, false]);
/// assert_eq!(demultiplexor_4way_1bit_gate(true, [true, true]), [false, false, false, true]);
/// ```
///
pub fn demultiplexor_4way_1bit_gate(a: bool, sel: [bool; 2]) -> [bool; 4] {
    [
        multiplexor_gate(a, false, or_gate(sel[0], sel[1])),
        multiplexor_gate(a, false, or_gate(sel[0], not_gate(sel[1]))),
        multiplexor_gate(a, false, or_gate(not_gate(sel[0]), sel[1])),
        multiplexor_gate(false, a, and_gate(sel[0], sel[1])),
    ]
}

/// The chopping 8-Way 1-Bit Demultiplexor gate. Output is 8 bits, with input in
/// first position if selector is 000, second position for 001, third position for 010,
/// fourth position for 011, fifth for 100, sixth for 101, seventh for 110, eighth for
/// 111. Unselected positions are always 0.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::demultiplexor_8way_1bit_gate;
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [false, false, false]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [false, false, true]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [false, true, false]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [false, true, true]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [true, false, false]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [true, false, true]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [true, true, false]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(false, [true, true, true]), [false, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [false, false, false]), [true, false, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [false, false, true]), [false, true, false, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [false, true, false]), [false, false, true, false, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [false, true, true]), [false, false, false, true, false, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [true, false, false]), [false, false, false, false, true, false, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [true, false, true]), [false, false, false, false, false, true, false, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [true, true, false]), [false, false, false, false, false, false, true, false]);
/// assert_eq!(demultiplexor_8way_1bit_gate(true, [true, true, true]), [false, false, false, false, false, false, false, true]);
/// ```
///
pub fn demultiplexor_8way_1bit_gate(a: bool, sel: [bool; 3]) -> [bool; 8]{
    let left_four_bit = and_gate(a, not_gate(sel[0]));
    let right_four_bit = and_gate(a, sel[0]);
    let left_four_solution = demultiplexor_4way_1bit_gate(left_four_bit, [sel[1], sel[2]]);
    let right_four_solution =
        demultiplexor_4way_1bit_gate(right_four_bit, [sel[1], sel[2]]);
    [
        left_four_solution[0],
        left_four_solution[1],
        left_four_solution[2],
        left_four_solution[3],
        right_four_solution[0],
        right_four_solution[1],
        right_four_solution[2],
        right_four_solution[3],
    ]
}

/// The choosy Multiplexor gate. Selector at 0 selects first element and 1 the second element.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::multiplexor_gate;
/// assert_eq!(multiplexor_gate(false, false, false), false);
/// assert_eq!(multiplexor_gate(false, true, false), false);
/// assert_eq!(multiplexor_gate(true, false, false), true);
/// assert_eq!(multiplexor_gate(true, true, false), true);
/// assert_eq!(multiplexor_gate(false, false, true), false);
/// assert_eq!(multiplexor_gate(false, true, true), true);
/// assert_eq!(multiplexor_gate(true, false, true), false);
/// assert_eq!(multiplexor_gate(true, true, true), true);
/// ```
///
pub fn multiplexor_gate(a: bool, b: bool, sel: bool) -> bool {
    let a_masked = and_gate(a, not_gate(sel));
    let b_masked = and_gate(b, sel);
    or_gate(a_masked, b_masked)
}

/// The all-the-choice-in-the-world Multi-Bit Multiplexor gate. Picks the first multi-bit array if selector 0,
/// and the second if selector 1.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::multiplexor_multibit_gate;
/// assert_eq!(
///     multiplexor_multibit_gate(
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///         false
///     ),
///     [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false]
/// );
///
/// assert_eq!(
///     multiplexor_multibit_gate(
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///         true
///     ),
///     [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
/// );
pub fn multiplexor_multibit_gate(a: [bool; 16], b: [bool; 16], sel: bool) -> [bool; 16] {
    [
        multiplexor_gate(a[0], b[0], sel),
        multiplexor_gate(a[1], b[1], sel),
        multiplexor_gate(a[2], b[2], sel),
        multiplexor_gate(a[3], b[3], sel),
        multiplexor_gate(a[4], b[4], sel),
        multiplexor_gate(a[5], b[5], sel),
        multiplexor_gate(a[6], b[6], sel),
        multiplexor_gate(a[7], b[7], sel),
        multiplexor_gate(a[8], b[8], sel),
        multiplexor_gate(a[9], b[9], sel),
        multiplexor_gate(a[10], b[10], sel),
        multiplexor_gate(a[11], b[11], sel),
        multiplexor_gate(a[12], b[12], sel),
        multiplexor_gate(a[13], b[13], sel),
        multiplexor_gate(a[14], b[14], sel),
        multiplexor_gate(a[15], b[15], sel),
    ]
}

/// The complexly choosy 4-way 16-bit Multiplexor gate. 00 selector is first element, 01 second,
/// 10 third, 11 fourth
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::multiplexor_4way_16bit_gate;
/// let inputs = [
///     [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///     [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///     [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
/// ];
///
/// assert_eq!(multiplexor_4way_16bit_gate(inputs, [false, false]), inputs[0]);
/// assert_eq!(multiplexor_4way_16bit_gate(inputs, [false, true]), inputs[1]);
/// assert_eq!(multiplexor_4way_16bit_gate(inputs, [true, false]), inputs[2]);
/// assert_eq!(multiplexor_4way_16bit_gate(inputs, [true, true]), inputs[3]);
///
pub fn multiplexor_4way_16bit_gate(a: [[bool; 16]; 4], sel: [bool; 2]) -> [bool; 16] {
    let left_two_pick = multiplexor_multibit_gate(a[0], a[1], sel[1]);
    let right_two_pick = multiplexor_multibit_gate(a[2], a[3], sel[1]);
    multiplexor_multibit_gate(left_two_pick, right_two_pick, sel[0])
}

/// The intricately choosy 8-way 16-bit Multiplexor gate. 000 selector is first element, 001 second,
/// 010 third, 011 fourth, 100 fifth, 101 sixth, 110 seventh, 111 eighth.
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::multiplexor_8way_16bit_gate;
/// let inputs = [
///     [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///     [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///     [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
///     [true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
///     [true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
///     [true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false],
///     [true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false],
/// ];
///
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [false, false, false]), inputs[0]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [false, false, true]), inputs[1]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [false, true, false]), inputs[2]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [false, true, true]), inputs[3]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [true, false, false]), inputs[4]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [true, false, true]), inputs[5]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [true, true, false]), inputs[6]);
/// assert_eq!(multiplexor_8way_16bit_gate(inputs, [true, true, true]), inputs[7]);
///
pub fn multiplexor_8way_16bit_gate(a: [[bool; 16]; 8], sel: [bool; 3]) -> [bool; 16] {
    let left_four_pick =
        multiplexor_4way_16bit_gate([a[0], a[1], a[2], a[3]], [sel[1], sel[2]]);
    let right_four_pick =
        multiplexor_4way_16bit_gate([a[4], a[5], a[6], a[7]], [sel[1], sel[2]]);
    multiplexor_multibit_gate(left_four_pick, right_four_pick, sel[0])
}

/// The always contradictory Not gate
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::not_gate;
/// assert_eq!(not_gate(true), false);
/// assert_eq!(not_gate(false), true);
/// ```
///
pub fn not_gate(input: bool) -> bool {
    nand_gate(true, input)
}

/// The always cranky Multi-Bit Not gate. NOT gate operation at each position.
/// # Examples
///
/// ```
/// use hack_kernel::gates::not_multibit_gate;
/// assert_eq!(
///     not_multibit_gate([true, false, true, true, false, false, true, false, true, true, true, false, false, false, true, false]),
///     [false, true, false, false, true, true, false, true, false, false, false, true, true, true, false, true]
/// )
/// ```
///
pub fn not_multibit_gate(a: [bool; 16]) -> [bool; 16] {
    [
        not_gate(a[0]),
        not_gate(a[1]),
        not_gate(a[2]),
        not_gate(a[3]),
        not_gate(a[4]),
        not_gate(a[5]),
        not_gate(a[6]),
        not_gate(a[7]),
        not_gate(a[8]),
        not_gate(a[9]),
        not_gate(a[10]),
        not_gate(a[11]),
        not_gate(a[12]),
        not_gate(a[13]),
        not_gate(a[14]),
        not_gate(a[15]),
    ]
}


/// The lovely Or gate
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::or_gate;
/// assert_eq!(or_gate(false, false), false);
/// assert_eq!(or_gate(true, false), true);
/// assert_eq!(or_gate(false, true), true);
/// assert_eq!(or_gate(true, true), true);
/// ```
///
pub fn or_gate(a: bool, b: bool) -> bool {
    let x = not_gate(a);
    let y = not_gate(b);
    nand_gate(x, y)
}

/// The I-take-almost-anything Multi-Bit Or gate. OR gate operation at each position.
/// # Examples
///
/// ```
/// use hack_kernel::gates::or_multibit_gate;
/// assert_eq!(
///     or_multibit_gate(
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
///     ),
///     [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false]
/// )
pub fn or_multibit_gate(a: [bool; 16], b: [bool; 16]) -> [bool; 16] {
    [
        or_gate(a[0], b[0]),
        or_gate(a[1], b[1]),
        or_gate(a[2], b[2]),
        or_gate(a[3], b[3]),
        or_gate(a[4], b[4]),
        or_gate(a[5], b[5]),
        or_gate(a[6], b[6]),
        or_gate(a[7], b[7]),
        or_gate(a[8], b[8]),
        or_gate(a[9], b[9]),
        or_gate(a[10], b[10]),
        or_gate(a[11], b[11]),
        or_gate(a[12], b[12]),
        or_gate(a[13], b[13]),
        or_gate(a[14], b[14]),
        or_gate(a[15], b[15]),
    ]
}

/// The there-can-only-be-one Multi-Way Or gate. Returns 1 if at least one input element is 1.
/// Otherwise 0.
/// # Examples
///
/// ```
/// use hack_kernel::gates::or_multiway_gate;
/// assert_eq!(
///     or_multiway_gate([false, false, false, false, false, false, false, false]),
///     false
/// );
///
/// assert_eq!(
///     or_multiway_gate([true, false, false, false, false, false, false, false]),
///     true
/// );
///
/// assert_eq!(
///     or_multiway_gate([false, false, false, false, false, false, false, true]),
///     true
/// );
pub fn or_multiway_gate(a: [bool; 8]) -> bool {
    or_gate(
        a[0],
        or_gate(
            a[1],
            or_gate(
                a[2],
                or_gate(
                    a[3],
                    or_gate(a[4], or_gate(a[5], or_gate(a[6], a[7]))),
                ),
            ),
        ),
    )
}

/// The always different XOr gate
///
/// # Examples
///
/// ```
/// use hack_kernel::gates::xor_gate;
/// assert_eq!(xor_gate(false, false), false);
/// assert_eq!(xor_gate(true, false), true);
/// assert_eq!(xor_gate(false, true), true);
/// assert_eq!(xor_gate(true, true), false);
/// ```
///
pub fn xor_gate(a: bool, b: bool) -> bool {
    and_gate(
        or_gate(a, b),
        nand_gate(a, b),
    )
}

/// The mysterious Multibit XOR gate. Does the XOR operation at each position.
/// 
/// This wasn't asked for in the book, but proved useful for Chapter 2. This gate makes it very easy
/// to toggle a not gate but setting input bus to all 1s (if bus is all 0s, input won't be changed).
/// 
/// # Examples
///
/// ```
/// use hack_kernel::gates::xor_multibit_gate;
/// assert_eq!(
///     xor_multibit_gate(
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
///     ),
///     [false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, ]
/// )
pub fn xor_multibit_gate(a: [bool; 16], b: [bool; 16]) -> [bool; 16] {
    [
        xor_gate(a[0], b[0]),
        xor_gate(a[1], b[1]),
        xor_gate(a[2], b[2]),
        xor_gate(a[3], b[3]),
        xor_gate(a[4], b[4]),
        xor_gate(a[5], b[5]),
        xor_gate(a[6], b[6]),
        xor_gate(a[7], b[7]),
        xor_gate(a[8], b[8]),
        xor_gate(a[9], b[9]),
        xor_gate(a[10], b[10]),
        xor_gate(a[11], b[11]),
        xor_gate(a[12], b[12]),
        xor_gate(a[13], b[13]),
        xor_gate(a[14], b[14]),
        xor_gate(a[15], b[15]),
    ]
}