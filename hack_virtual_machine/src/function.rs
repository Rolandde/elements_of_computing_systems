//! Assembly code for VM function calls.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Standalone assembly block that initializes local variables on the stack to 0.
///
/// Assumes the number of vars is in the D register.
pub fn local_vars() {
    [
        Assembly::Label("LOCAL_VARS".to_string()),
        CCommand::new_dest(CDest::D, CComp::DMinusOne).into(),
        ACommand::Symbol("LOCAL_END".to_string()).into(),
        CCommand::new_jump(CComp::D, CJump::Less).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::Zero).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        ACommand::Symbol("LOCAL_VARS".to_string()).into(),
        CCommand::new_jump(CComp::One, CJump::Jump).into(),
        Assembly::Label("LOCAL_END".to_string()),
    ];
}
