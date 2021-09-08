//! # Arithmetic Gates
//!
//! Implementing arithmetic gates, leading up to the Arithmetic Logical Unit (Chapter 2 of the book).
//!
//! ## Half-Adder
//! The book gives away the solution (use AND and XOR gate)
//!
//! ## Full-Adder
//! The book hint was 2 Half-Adders and a simple gate. Trial and error got the solution. The
//! solution makes sense in hindsight. Half-add any two numbers. If the carry bit is set, then
//! it will be set in the final answer (sum is 2 or 3). Then take the sum and add it to the third number
//! using another Half-Adder. The sum of that is the final sum result. Run an OR gate on the two
//! carry outputs to get the final carry result.
//!
//! ## Add
//! Use Full-Adder sixteen times, taking the carry to the next gate call (first carry is 0).
//!
//! # Add-One
//! Trivial convenience gate
//!
//! # The Arithmetic Logic Unit
//! The interesting part was using single bits to cause different calculations without having an if statement.
//! For setting to 0, an AND gate works. Negation was interesting, as the cleanest solution I could think of was
//! a multiway XOR gate, but its implementation was not asked for in Chapter 1. Picking between addition or an
//! AND gate was done through a multiplexor, which is very inefficient as both calculations have to occur.
//!
//! # Examples
//! ```
//! use rust_elements_computing_systems::{from_i16, gates, arithmetic as alu};
//! let x = from_i16(22);
//! let y = from_i16(42);
//!
//! // Constant ALU operations
//! assert_eq!(alu::alu(x, y, alu::ALU_ZERO), (from_i16(0), true, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_ONE), (from_i16(1), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_MINUS_ONE), (from_i16(-1), false, true));
//! 
//! // Single input ALU operations
//! assert_eq!(alu::alu(x, y, alu::ALU_X), (from_i16(22), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_Y), (from_i16(42), false, false));
//! assert_eq!(
//!     alu::alu(x, y, alu::ALU_X_NOT), 
//!     (gates::not_multibit_gate(x), false, true)
//! );
//! assert_eq!(
//!     alu::alu(x, y, alu::ALU_Y_NOT), 
//!     (gates::not_multibit_gate(y), false, true)
//! );
//! assert_eq!(alu::alu(x, y, alu::ALU_X_MINUS), (from_i16(-22), false, true));
//! assert_eq!(alu::alu(x, y, alu::ALU_Y_MINUS), (from_i16(-42), false, true));
//! assert_eq!(alu::alu(x, y, alu::ALU_X_PLUS1), (from_i16(23), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_Y_PLUS1), (from_i16(43), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_X_MINUS1), (from_i16(21), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_Y_MINUS1), (from_i16(41), false, false));
//! 
//! // Arithmetic ALU operations
//! assert_eq!(alu::alu(x, y, alu::ALU_X_PLUS_Y), (from_i16(64), false, false));
//! assert_eq!(alu::alu(x, y, alu::ALU_X_MINUS_Y), (from_i16(-20), false, true));
//! assert_eq!(alu::alu(x, y, alu::ALU_Y_MINUS_X), (from_i16(20), false, false));
//! assert_eq!(alu::alu(y, y, alu::ALU_Y_MINUS_X), (from_i16(0), true, false));
//! 
//! // Bitwise ALU operations
//! assert_eq!(
//!     alu::alu(x, y, alu::ALU_X_AND_Y), 
//!     (gates::and_multibit_gate(x, y), false, false)
//! );
//! assert_eq!(
//!     alu::alu(x, y, alu::ALU_X_OR_Y), 
//!     (gates::or_multibit_gate(x, y), false, false)
//! );
//! ```

use crate::gates;

/// The studious Half-Adder gate. Left output bit is carry, right sum.
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::arithmetic::half_adder;
/// assert_eq!(half_adder(false, false), [false, false]);
/// assert_eq!(half_adder(false, true), [false, true]);
/// assert_eq!(half_adder(true, false), [false, true]);
/// assert_eq!(half_adder(true, true), [true, false]);
/// ```
///
pub fn half_adder(a: bool, b: bool) -> [bool; 2] {
    [gates::and_gate(a, b), gates::xor_gate(a, b)]
}

/// The genius Full Adder gate. Adds three bits together, with the left output
/// bit being the carry and the right the sum
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::arithmetic::full_adder;
/// assert_eq!(full_adder(false, false, false), [false, false]);
/// assert_eq!(full_adder(false, false, true), [false, true]);
/// assert_eq!(full_adder(false, true, false), [false, true]);
/// assert_eq!(full_adder(false, true, true), [true, false]);
/// assert_eq!(full_adder(true, false, false), [false, true]);
/// assert_eq!(full_adder(true, false, true), [true, false]);
/// assert_eq!(full_adder(true, true, false), [true, false]);
/// assert_eq!(full_adder(true, true, true), [true, true]);
///
pub fn full_adder(a: bool, b: bool, c: bool) -> [bool; 2] {
    let [carry, sum] = half_adder(a, b);
    let [carry2, final_sum] = half_adder(sum, c);
    [gates::or_gate(carry, carry2), final_sum]
}

/// The suave Add gate
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, arithmetic::add};
/// let ten = from_i16(10);
/// let twenty = from_i16(20);
/// let minus_ten = from_i16(-10);
/// let zero = from_i16(0);
/// assert_eq!(add(ten, ten), twenty);
/// assert_eq!(add(ten, minus_ten), zero);
/// assert_eq!(add(twenty, minus_ten), ten);
/// assert_eq!(add(twenty, zero), twenty);

pub fn add(a: [bool; 16], b: [bool; 16]) -> [bool; 16] {
    // The for loop is cheating a little, but I don't care
    let mut carry = false;
    let mut result = [false; 16];
    for i in (0..a.len()).rev() {
        let [c, s] = full_adder(a[i], b[i], carry);
        result[i] = s;
        carry = c;
    }
    result
}

/// The one-step-at-a-time Add One gate
///
/// # Examples
/// ```
/// use rust_elements_computing_systems::{from_i16, arithmetic::add_one};
/// assert_eq!(add_one(from_i16(42)), from_i16(43));
/// assert_eq!(add_one(from_i16(-42)), from_i16(-41));
///
pub fn add_one(a: [bool; 16]) -> [bool; 16] {
    let one = [
        false, false, false, false, false, false, false, false, false, false, false, false, false,
        false, false, true,
    ];
    add(a, one)
}

/// The final boss ALU. Flag bits are documented as constants. Output is 16-bit calculation,
/// 1 iff output=0, 1 iff output <0.
///
/// Examples at the top of the page.
pub fn alu(x: [bool; 16], y: [bool; 16], flag: [bool; 6]) -> ([bool; 16], bool, bool) {
    let mut x = gates::and_multibit_gate(x, [gates::not_gate(flag[0]); 16]);
    x = gates::xor_multibit_gate(x, [flag[1]; 16]);

    let mut y = gates::and_multibit_gate(y, [gates::not_gate(flag[2]); 16]);
    y = gates::xor_multibit_gate(y, [flag[3]; 16]);

    // Addition and OR are both calculated and then only one is picked
    // There must be a more efficient way
    let addition = add(x, y);
    let and = gates::and_multibit_gate(x, y);
    let mut f = gates::multiplexor_multibit_gate(and, addition, flag[4]);
    f = gates::xor_multibit_gate(f, [flag[5]; 16]);

    // Have to split in two, as gate only works on 8 bits
    let zero_check_1 = gates::or_multiway_gate([f[0], f[1], f[2], f[3], f[4], f[5], f[6], f[7]]);
    let zero_check_2 =
        gates::or_multiway_gate([f[8], f[9], f[10], f[11], f[12], f[13], f[14], f[15]]);
    let zero = gates::not_gate(gates::or_gate(zero_check_1, zero_check_2));

    (f, zero, f[0])
}

/// Returns 0
pub const ALU_ZERO: [bool; 6] = [true, false, true, false, true, false];
/// Returns 1
pub const ALU_ONE: [bool; 6] = [true, true, true, true, true, true];
/// Returns -1
pub const ALU_MINUS_ONE: [bool; 6] = [true, true, true, false, true, false];
/// Returns X 
pub const ALU_X: [bool; 6] = [false, false, true, true, false, false];
/// Returns Y 
pub const ALU_Y: [bool; 6] = [true, true, false, false, false, false];
/// Returns NOT(X)
pub const ALU_X_NOT: [bool; 6] = [false, false, true, true, false, true];
/// Returns NOT(Y)
pub const ALU_Y_NOT: [bool; 6] = [true, true, false, false, false, true];
/// Returns minus X
pub const ALU_X_MINUS: [bool; 6] = [false, false, true, true, true, true];
/// Returns minus Y
pub const ALU_Y_MINUS: [bool; 6] = [true, true, false, false, true, true];
/// Returns X+1
pub const ALU_X_PLUS1: [bool; 6] = [false, true, true, true, true, true];
/// Returns Y+1
pub const ALU_Y_PLUS1: [bool; 6] = [true, true, false, true, true, true];
/// Returns X+1
pub const ALU_X_MINUS1: [bool; 6] = [false, false, true, true, true, false];
/// Returns Y+1
pub const ALU_Y_MINUS1: [bool; 6] = [true, true, false, false, true, false];
/// Returns X+Y
pub const ALU_X_PLUS_Y: [bool; 6] = [false, false, false, false, true, false];
/// Returns X-Y
pub const ALU_X_MINUS_Y: [bool; 6] = [false, true, false, false, true, true];
/// Returns Y-X
pub const ALU_Y_MINUS_X: [bool; 6] = [false, false, false, true, true, true];
/// Returns AND(X, Y)
pub const ALU_X_AND_Y: [bool; 6] = [false, false, false, false, false, false];
/// Returns OR(X, Y)
pub const ALU_X_OR_Y: [bool; 6] = [false, true, false, true, false, true];

#[cfg(test)]
mod alu_tests {
    use super::*;
    use crate::from_i16;
    #[test]
    fn subtraction(){
        assert_eq!(
            alu(from_i16(100), from_i16(18), ALU_X_MINUS_Y),
            (from_i16(82), false, false)
        );

        assert_eq!(
            alu(from_i16(100), from_i16(18), ALU_Y_MINUS_X),
            (from_i16(-82), false, true)
        );

        assert_eq!(
            alu(from_i16(100), from_i16(-18), ALU_X_MINUS_Y),
            (from_i16(118), false, false)
        );
    }

    #[test]
    fn negative() {
        assert_eq!(
            alu(from_i16(10000), from_i16(3999), ALU_X_MINUS),
            (from_i16(-10000), false, true)
        );

        assert_eq!(
            alu(from_i16(10000), from_i16(-3999), ALU_Y_MINUS),
            (from_i16(3999), false, false)
        );

        assert_eq!(
            alu(from_i16(10000), from_i16(0), ALU_Y_MINUS),
            (from_i16(0), true, false)
        );
    }
}