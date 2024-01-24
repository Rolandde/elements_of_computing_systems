use std::convert::Into;

use crate::SegmentIndex;
use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

pub fn segment_to_a_register(segment: SegmentIndex, assembly: &mut Vec<Assembly>) {
    let base: Assembly = match segment {
        SegmentIndex::Argument(_) => ReservedSymbols::ARG.into(),
    };
}
