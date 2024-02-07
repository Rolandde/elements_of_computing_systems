//! Assembly code for VM memory access.
//!
//! Memory access is interesting, because there is an index that requires a calculation. Using only the A and D registers puts a hard limitaiton on index calculations. If D is storing a value for later, you cannot do any math with the A register that isn't +/- 1. Having D hold the address to write to and A hold the value doesn't work, as there is no way to switch those two without a third storage location.
//! The `push` command is within this limitation. The value of the segment is stored in D and no math is required to get the top of the stack, as it is already in @SP.
//! ```text
//! // push local 2
//! @LCL // Address holding the base address of the local segment
//! D=M // D holds base address of the local segment
//! @2 // Index offset
//! A=D+A // A now holds address of the value to push onto the stack
//! D=M  // D holds the value to push onto the stack
//! @SP // Address holding the address of the top of the stack
//! A=M // A holds the address of the top of the stack
//! M=D // Write value onto the top of the stack
//! D=A+1 // Increment the address of the top of the stack by one
//! @SP // The address that holds the address of the top of the stack
//! M=D // The address of the top of the stack is now one higher
//! ```
//! The `pop` command breaks under this limitation. If you store the popped value from the stack in D, you cannot do the math to get the segment address to write that value to.
//! ```text
//! // pop local 2
//! @SP // Holds the top of the stack
//! A=M-1 // Get address of the top most stack value
//! D=M // D holds the value at the top of the stack
//! @LCL // Address that holds base address of the local segment
//! D=M // Need to store the address of the local segment for +2 addition. This overwrites the value that needs to be written
//! @2 // This is the +2 addition, which goes into the A register
//! ```
//! If you store the segment address into D, then A holds the value to write to the segment address. The registers than have to switch their content, which cannot be done without a third memory address.
//! ```text
//! // pop local 2
//! @LCL // Address holding the base address of the local segment
//! D=M // D holds base address of the local segment
//! @2 // Index offset
//! D=D+A // D now holds address to write from the stack to
//! @SP // Holds the top of the stack
//! A=M-1 // Get address of the top most stack value
//! A=M // A stores the value to write to address in D
//! A=D // A now has the address to write to, but it held the value to write, which is now lost
//! ```
//! So at least one other memory address is required to get this to work. As luck would have it, we have R13-R15 for the VM. Yay, let's use one of them.
//!
//! Fun simple exception: `pointer` and `temp` segment aren't pointers, but actuall memory addresses (R3-R12). They don't need an offset, so make slighlty easier assembly code.

use std::convert::Into;

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, ReservedSymbols};
use hack_assembler::Assembly;

/// Segments that are pointers with offsets.
pub enum SegmentPointer {
    Argument(i16),
    Local(i16),
    This(i16),
    That(i16),
}

/// Push onto the stack from a pointer.
///
/// The function asssumes a base that is a pointer (ARG, LCL, THIS, THAT). Other reserved symbol won't cause an error, but you will get wrong behaviour. Other reserved symbols aren't pointers, so dereferencing them (which this function does) will lead you to strange places.
pub fn push_pointer(base: ReservedSymbols, offset: i16) -> [Assembly; 11] {
    [
        base.into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Address(offset).into(),
        CCommand::new_dest(CDest::A, CComp::DPlusA).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Push onto the stack from the static segment.
pub fn push_static(offset: i16) -> [Assembly; 8] {
    [
        ACommand::Address(crate::STATIC_START + offset).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Push the value at that address onto the stack
pub fn push_value(from: ReservedSymbols) -> [Assembly; 8] {
    [
        from.into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Pop a value from the stack from a pointer.
///
/// The function assumes a base that is a pointer (ARG, LCL, THIS, THAT). So same warning as [push_pointer] if you break that assumption.
pub fn pop_pointer(base: ReservedSymbols, offset: i16) -> [Assembly; 12] {
    [
        base.into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Address(offset).into(),
        CCommand::new_dest(CDest::D, CComp::DPlusA).into(),
        crate::MEM_POP.into(),                         // Address to write to
        CCommand::new_dest(CDest::M, CComp::D).into(), // is saved to all purpose register
        ReservedSymbols::SP.into(),
        // The next two instructions set M[0] to the top stack address and then set the A register to that address. Are you tempted to write MA=M-1?
        // Don't. The CPU sets A register and then instructs the computer to write to that memory
        // You'd be writing the top of the stack address at that address (M[288] = 288)
        CCommand::new_dest(CDest::M, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        crate::MEM_POP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/*
# push local 2
@LCL
D=M
@2
A=D+A
D=M
@SP
A=M
M=D
D=A+1
@SP
M=D
*/

/*
# pop local 3
@SP
M=M-1
A=M
D=M
@LCL
A=M+3
M=D
*/

/*
# pop local 3
@SP
M=M-1
A=M
D=M
@LCL

*/

/*
# push temp 3
@R8
D=M
@SP
A=M
M=D
D=A+1
@SP
M=D
*/

/*
# pop pointer 2
@SP
M=M-1
A=M
D=M
@THAT
M=D
*/