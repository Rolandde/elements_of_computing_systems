//! # Gate Implementation
//!
//! Implementing gates using only `NAND` (Not And) and any gates derived using `NAND` (Section 1.3).
//! As `NAND` is magically given, the Rust bitwise operations are used to construct the gate. All other
//! gates did not use any Rust logic at all (assignment were used for code readability). The gates were
//! implemented in order given in the book, which made puzzling them out easier.
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
//! NOT(OR)
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
//! are one bit for one selector and the other bit for the other three selectors. For 00, that would be XOR 
//! (true for 00, false for all others). Demultiplexors can then be used to slot the input bit into the right
//! position.
//! 
//! ## 8-way 1-bit Demultiplexor gate
//! This was done differently that the 4-way gate. Rather than use a Multiplexor and tediously construct eight
//! unique flags that place the input flag in the right position, two 4-way Demultiplexors were used. The trick
//! in that approach was to use the first selector bit to turn off the input bit for the appropriate 
//! 4-way Demultiplexor. 

pub trait Gate {
    type In;
    type Out;

    fn calc(input: Self::In) -> Self::Out;
}

/// The Not And gate. The only gate that is implemented with Rust bitwise operators.
/// All other gate logic will use only other gates.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{NandGate, Gate};
/// assert_eq!(NandGate::calc([false, false]), true);
/// assert_eq!(NandGate::calc([true, false]), true);
/// assert_eq!(NandGate::calc([false, true]), true);
/// assert_eq!(NandGate::calc([true, true]), false);
/// ```
///
pub struct NandGate;

impl Gate for NandGate {
    type In = [bool; 2];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        !(input[0] & input[1])
    }
}

/// The beloved And gate.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{AndGate, Gate};
/// assert_eq!(AndGate::calc([false, false]), false);
/// assert_eq!(AndGate::calc([true, false]), false);
/// assert_eq!(AndGate::calc([false, true]), false);
/// assert_eq!(AndGate::calc([true, true]), true);
/// ```
///
pub struct AndGate;

impl Gate for AndGate {
    type In = [bool; 2];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        NotGate::calc(NandGate::calc(input))
    }
}

/// The divisive Demultiplexor gate. Input (first element), selector (second element).
/// For output, if selector=0 then [input, 0] else [0, input]. In words, put input in
/// first or second position of output given the selector.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{DemultiplexorGate, Gate};
/// assert_eq!(DemultiplexorGate::calc([false, false]), [false, false]);
/// assert_eq!(DemultiplexorGate::calc([true, false]), [true, false]);
/// assert_eq!(DemultiplexorGate::calc([false, true]), [false, false]);
/// assert_eq!(DemultiplexorGate::calc([true, true]), [false, true]);
/// ```
///
pub struct DemultiplexorGate;

impl Gate for DemultiplexorGate {
    type In = [bool; 2];
    type Out = [bool; 2];

    fn calc(input: Self::In) -> Self::Out {
        [
            MultiplexorGate::calc([input[0], false, input[1]]),
            MultiplexorGate::calc([false, input[0], input[1]]),
        ]
    }
}
/// The quartering 4-Way 1-Bit Demultiplexor gate. Output is 4 bits, with input in
/// first position if selector is 00, second position for 01, third position for 10,
/// fourth position for 11. Unselected positions are always 0.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{Demultiplexor4Way1BitGate, Gate};
/// assert_eq!(Demultiplexor4Way1BitGate::calc((false, [false, false])), [false, false, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((false, [false, true])), [false, false, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((false, [true, false])), [false, false, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((false, [true, true])), [false, false, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((true, [false, false])), [true, false, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((true, [false, true])), [false, true, false, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((true, [true, false])), [false, false, true, false]);
/// assert_eq!(Demultiplexor4Way1BitGate::calc((true, [true, true])), [false, false, false, true]);
/// ```
///
pub struct Demultiplexor4Way1BitGate;

impl Gate for Demultiplexor4Way1BitGate {
    type In = (bool, [bool; 2]);
    type Out = [bool; 4];

    fn calc(input: Self::In) -> Self::Out {
        let (ins, sel) = input;
        [
            MultiplexorGate::calc([false, ins, XOrGate::calc([sel[0], sel[1]])]),
            MultiplexorGate::calc([false, ins, XOrGate::calc([sel[0], NotGate::calc(sel[1])])]),
            MultiplexorGate::calc([false, ins, XOrGate::calc([NotGate::calc(sel[0]), sel[1]])]),
            MultiplexorGate::calc([false, ins, AndGate::calc([sel[0], sel[1]])]),
        ]
    }
}

/// The chopping 8-Way 1-Bit Demultiplexor gate. Output is 8 bits, with input in
/// first position if selector is 000, second position for 001, third position for 010,
/// fourth position for 011, fifth for 100, sixth for 101, seventh for 110, eighth for 
/// 111. Unselected positions are always 0.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{Demultiplexor8Way1BitGate, Gate};
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [false, false, false])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [false, false, true])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [false, true, false])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [false, true, true])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [true, false, false])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [true, false, true])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [true, true, false])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((false, [true, true, true])), [false, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [false, false, false])), [true, false, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [false, false, true])), [false, true, false, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [false, true, false])), [false, false, true, false, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [false, true, true])), [false, false, false, true, false, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [true, false, false])), [false, false, false, false, true, false, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [true, false, true])), [false, false, false, false, false, true, false, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [true, true, false])), [false, false, false, false, false, false, true, false]);
/// assert_eq!(Demultiplexor8Way1BitGate::calc((true, [true, true, true])), [false, false, false, false, false, false, false, true]);
/// ```
///
pub struct Demultiplexor8Way1BitGate;

impl Gate for Demultiplexor8Way1BitGate {
    type In = (bool, [bool; 3]);
    type Out = [bool; 8];

    fn calc(input: Self::In) -> Self::Out {
        let (ins, sel) = input;
        let left_four_bit = AndGate::calc([ins, NotGate::calc(sel[0])]);
        let right_four_bit = AndGate::calc([ins, sel[0]]);
        let left_four_solution = Demultiplexor4Way1BitGate::calc((left_four_bit, [sel[1], sel[2]]));
        let right_four_solution = Demultiplexor4Way1BitGate::calc((right_four_bit, [sel[1], sel[2]]));
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
}

/// The can-do-it-all Multi-Bit And gate
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiBitAndGate, Gate};
/// assert_eq!(
///     MultiBitAndGate::calc([
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
///     ]),
///     [true, false, false, false, true, false, false, false, true, false, false, false, true, false, false, false]
/// )

pub struct MultiBitAndGate;

impl Gate for MultiBitAndGate {
    type In = [[bool; 16]; 2];
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        [
            AndGate::calc([input[0][0], input[1][0]]),
            AndGate::calc([input[0][1], input[1][1]]),
            AndGate::calc([input[0][2], input[1][2]]),
            AndGate::calc([input[0][3], input[1][3]]),
            AndGate::calc([input[0][4], input[1][4]]),
            AndGate::calc([input[0][5], input[1][5]]),
            AndGate::calc([input[0][6], input[1][6]]),
            AndGate::calc([input[0][7], input[1][7]]),
            AndGate::calc([input[0][8], input[1][8]]),
            AndGate::calc([input[0][9], input[1][9]]),
            AndGate::calc([input[0][10], input[1][10]]),
            AndGate::calc([input[0][11], input[1][11]]),
            AndGate::calc([input[0][12], input[1][12]]),
            AndGate::calc([input[0][13], input[1][13]]),
            AndGate::calc([input[0][14], input[1][14]]),
            AndGate::calc([input[0][15], input[1][15]]),
        ]
    }
}

/// The all-the-choice-in-the-world Multi-Bit Multiplexor gate
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiBitMultiplexorGate, Gate};
/// assert_eq!(
///     MultiBitMultiplexorGate::calc((
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///         false
///     )),
///     [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false]
/// );
///
/// assert_eq!(
///     MultiBitMultiplexorGate::calc((
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///         true
///     )),
///     [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
/// );
pub struct MultiBitMultiplexorGate;

impl Gate for MultiBitMultiplexorGate {
    type In = ([bool; 16], [bool; 16], bool);
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        let (a, b, sel) = input;
        [
            MultiplexorGate::calc([a[0], b[0], sel]),
            MultiplexorGate::calc([a[1], b[1], sel]),
            MultiplexorGate::calc([a[2], b[2], sel]),
            MultiplexorGate::calc([a[3], b[3], sel]),
            MultiplexorGate::calc([a[4], b[4], sel]),
            MultiplexorGate::calc([a[5], b[5], sel]),
            MultiplexorGate::calc([a[6], b[6], sel]),
            MultiplexorGate::calc([a[7], b[7], sel]),
            MultiplexorGate::calc([a[8], b[8], sel]),
            MultiplexorGate::calc([a[9], b[9], sel]),
            MultiplexorGate::calc([a[10], b[10], sel]),
            MultiplexorGate::calc([a[11], b[11], sel]),
            MultiplexorGate::calc([a[12], b[12], sel]),
            MultiplexorGate::calc([a[13], b[13], sel]),
            MultiplexorGate::calc([a[14], b[14], sel]),
            MultiplexorGate::calc([a[15], b[15], sel]),
        ]
    }
}

/// The always cranky Multi-Bit Not gate
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiBitNotGate, Gate};
/// assert_eq!(
///     MultiBitNotGate::calc([true, false, true, true, false, false, true, false, true, true, true, false, false, false, true, false]),
///     [false, true, false, false, true, true, false, true, false, false, false, true, true, true, false, true]
/// )
/// ```
///

pub struct MultiBitNotGate;

impl Gate for MultiBitNotGate {
    type In = [bool; 16];
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        [
            NotGate::calc(input[0]),
            NotGate::calc(input[1]),
            NotGate::calc(input[2]),
            NotGate::calc(input[3]),
            NotGate::calc(input[4]),
            NotGate::calc(input[5]),
            NotGate::calc(input[6]),
            NotGate::calc(input[7]),
            NotGate::calc(input[8]),
            NotGate::calc(input[9]),
            NotGate::calc(input[10]),
            NotGate::calc(input[11]),
            NotGate::calc(input[12]),
            NotGate::calc(input[13]),
            NotGate::calc(input[14]),
            NotGate::calc(input[15]),
        ]
    }
}

/// The I-take-almost-anything Multi-Bit Or gate
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiBitOrGate, Gate};
/// assert_eq!(
///     MultiBitOrGate::calc([
///         [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///         [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false]
///     ]),
///     [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false]
/// )

pub struct MultiBitOrGate;

impl Gate for MultiBitOrGate {
    type In = [[bool; 16]; 2];
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        [
            OrGate::calc([input[0][0], input[1][0]]),
            OrGate::calc([input[0][1], input[1][1]]),
            OrGate::calc([input[0][2], input[1][2]]),
            OrGate::calc([input[0][3], input[1][3]]),
            OrGate::calc([input[0][4], input[1][4]]),
            OrGate::calc([input[0][5], input[1][5]]),
            OrGate::calc([input[0][6], input[1][6]]),
            OrGate::calc([input[0][7], input[1][7]]),
            OrGate::calc([input[0][8], input[1][8]]),
            OrGate::calc([input[0][9], input[1][9]]),
            OrGate::calc([input[0][10], input[1][10]]),
            OrGate::calc([input[0][11], input[1][11]]),
            OrGate::calc([input[0][12], input[1][12]]),
            OrGate::calc([input[0][13], input[1][13]]),
            OrGate::calc([input[0][14], input[1][14]]),
            OrGate::calc([input[0][15], input[1][15]]),
        ]
    }
}

/// The there-can-only-be-one Multi-Way Or gate
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiWayOrGate, Gate};
/// assert_eq!(
///     MultiWayOrGate::calc([false, false, false, false, false, false, false, false]),
///     false
/// );
///
/// assert_eq!(
///     MultiWayOrGate::calc([true, false, false, false, false, false, false, false]),
///     true
/// );
///
/// assert_eq!(
///     MultiWayOrGate::calc([false, false, false, false, false, false, false, true]),
///     true
/// );

pub struct MultiWayOrGate;

impl Gate for MultiWayOrGate {
    type In = [bool; 8];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        OrGate::calc([
            input[0],
            OrGate::calc([
                input[1],
                OrGate::calc([
                    input[2],
                    OrGate::calc([
                        input[3],
                        OrGate::calc([
                            input[4],
                            OrGate::calc([input[5], OrGate::calc([input[6], input[7]])]),
                        ]),
                    ]),
                ]),
            ]),
        ])
    }
}

/// The choosy Multiplexor gate. Last element is the selector, with 0 selecting first element
/// and 1 the second element.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{MultiplexorGate, Gate};
/// assert_eq!(MultiplexorGate::calc([false, false, false]), false);
/// assert_eq!(MultiplexorGate::calc([false, true, false]), false);
/// assert_eq!(MultiplexorGate::calc([true, false, false]), true);
/// assert_eq!(MultiplexorGate::calc([true, true, false]), true);
/// assert_eq!(MultiplexorGate::calc([false, false, true]), false);
/// assert_eq!(MultiplexorGate::calc([false, true, true]), true);
/// assert_eq!(MultiplexorGate::calc([true, false, true]), false);
/// assert_eq!(MultiplexorGate::calc([true, true, true]), true);
/// ```
///
pub struct MultiplexorGate;

impl Gate for MultiplexorGate {
    type In = [bool; 3];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        let a_masked = AndGate::calc([input[0], NotGate::calc(input[2])]);
        let b_masked = AndGate::calc([input[1], input[2]]);
        OrGate::calc([a_masked, b_masked])
    }
}

/// The complexly choosy 4-way 16-bit Multiplexor gate. 00 selector is first element, 01 second,
/// 10 third, 11 fourth
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{Multiplexor4Way16BitGate, Gate};
/// let inputs = [
///     [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false],
///     [true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false],
///     [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true],
///     [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
/// ];
///
/// assert_eq!(Multiplexor4Way16BitGate::calc((inputs, [false, false])), inputs[0]);
/// assert_eq!(Multiplexor4Way16BitGate::calc((inputs, [false, true])), inputs[1]);
/// assert_eq!(Multiplexor4Way16BitGate::calc((inputs, [true, false])), inputs[2]);
/// assert_eq!(Multiplexor4Way16BitGate::calc((inputs, [true, true])), inputs[3]);
///

pub struct Multiplexor4Way16BitGate;

impl Gate for Multiplexor4Way16BitGate {
    type In = ([[bool; 16]; 4], [bool; 2]);
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        let (ins, sel) = input;
        let left_two_pick = MultiBitMultiplexorGate::calc((ins[0], ins[1], sel[1]));
        let right_two_pick = MultiBitMultiplexorGate::calc((ins[2], ins[3], sel[1]));
        MultiBitMultiplexorGate::calc((left_two_pick, right_two_pick, sel[0]))
    }
}

/// The intricately choosy 8-way 16-bit Multiplexor gate. 000 selector is first element, 001 second,
/// 010 third, 011 fourth, 100 fifth, 101 sixth, 110 seventh, 111 eighth.
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{Multiplexor8Way16BitGate, Gate};
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
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [false, false, false])), inputs[0]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [false, false, true])), inputs[1]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [false, true, false])), inputs[2]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [false, true, true])), inputs[3]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [true, false, false])), inputs[4]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [true, false, true])), inputs[5]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [true, true, false])), inputs[6]);
/// assert_eq!(Multiplexor8Way16BitGate::calc((inputs, [true, true, true])), inputs[7]);
///

pub struct Multiplexor8Way16BitGate;

impl Gate for Multiplexor8Way16BitGate {
    type In = ([[bool; 16]; 8], [bool; 3]);
    type Out = [bool; 16];

    fn calc(input: Self::In) -> Self::Out {
        let (ins, sel) = input;
        let left_four_pick =
            Multiplexor4Way16BitGate::calc(([ins[0], ins[1], ins[2], ins[3]], [sel[1], sel[2]]));
        let right_four_pick =
            Multiplexor4Way16BitGate::calc(([ins[4], ins[5], ins[6], ins[7]], [sel[1], sel[2]]));
        MultiBitMultiplexorGate::calc((left_four_pick, right_four_pick, sel[0]))
    }
}

/// The always contradictory Not gate
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{NotGate, Gate};
/// assert_eq!(NotGate::calc(true), false);
/// assert_eq!(NotGate::calc(false), true);
/// ```
///
pub struct NotGate;

impl Gate for NotGate {
    type In = bool;
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        NandGate::calc([true, input])
    }
}

/// The lovely Or gate
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{OrGate, Gate};
/// assert_eq!(OrGate::calc([false, false]), false);
/// assert_eq!(OrGate::calc([true, false]), true);
/// assert_eq!(OrGate::calc([false, true]), true);
/// assert_eq!(OrGate::calc([true, true]), true);
/// ```
///
pub struct OrGate;

impl Gate for OrGate {
    type In = [bool; 2];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        let a = NotGate::calc(input[0]);
        let b = NotGate::calc(input[1]);
        NandGate::calc([a, b])
    }
}

/// The stately XOr gate
///
/// # Examples
///
/// ```
/// use rust_elements_computing_systems::gates::{XOrGate, Gate};
/// assert_eq!(XOrGate::calc([false, false]), true);
/// assert_eq!(XOrGate::calc([true, false]), false);
/// assert_eq!(XOrGate::calc([false, true]), false);
/// assert_eq!(XOrGate::calc([true, true]), false);
/// ```
///
pub struct XOrGate;

impl Gate for XOrGate {
    type In = [bool; 2];
    type Out = bool;

    fn calc(input: Self::In) -> Self::Out {
        NotGate::calc(OrGate::calc(input))
    }
}