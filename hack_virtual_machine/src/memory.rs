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

pub fn push_pointer(segment: SegmentPointer) -> [Assembly; 11] {
    let SegmentPoinerSplit { base, offset } = segment.split();
    [
        base.into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        offset.into(),
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

struct SegmentPoinerSplit {
    base: ACommand,
    offset: ACommand,
}

impl SegmentPointer {
    fn split(&self) -> SegmentPoinerSplit {
        match self {
            Self::Argument(i) => SegmentPoinerSplit {
                base: ReservedSymbols::ARG.into(),
                offset: ACommand::Address(*i),
            },
            Self::Local(i) => SegmentPoinerSplit {
                base: ReservedSymbols::LCL.into(),
                offset: ACommand::Address(*i),
            },
            Self::This(i) => SegmentPoinerSplit {
                base: ReservedSymbols::THIS.into(),
                offset: ACommand::Address(*i),
            },
            Self::That(i) => SegmentPoinerSplit {
                base: ReservedSymbols::THAT.into(),
                offset: ACommand::Address(*i),
            },
        }
    }
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
