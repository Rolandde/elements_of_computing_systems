use std::convert::Into;

use crate::SegmentIndex;
use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/*
# push local 1
@LCL
A=M+1
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

pub fn segment_to_a_register(segment: SegmentIndex, assembly: &mut Vec<Assembly>) {
    let base: Assembly = match segment {
        SegmentIndex::Argument(_) => ReservedSymbols::ARG.into(),
    };
}
