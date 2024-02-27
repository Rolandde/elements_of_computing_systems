//! Assembly code for VM function calls.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Standalone assembly block that initializes local variables on the stack to 0.
///
/// Assumes the number of vars is in the D register.
pub fn local_vars() -> [Assembly; 10] {
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
    ]
}

/// The assembly for the VM `call` command, which creates the frame and sets callee LCL and ARG.
///
/// Assumes that the A register is set to the return address that goes first on the stack.
///
/// There is no jump to the callee and no return label. The VM will add that assembly code.
pub fn call_stack(n_args: i16) -> [Assembly; 33] {
    // Args for callee are pushed on the stack before this call.
    // The ARG pointer for callee has to be set after the ARG pointer for the caller function has been stored
    // 5 comes from 5 values being put on the stack before the callee ARG pointer is set
    let reposition_arg_pointer = 5 + n_args;
    [
        // Return address
        CCommand::new_dest(CDest::D, CComp::A).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        // LCL pointer
        ACommand::Reserved(ReservedSymbols::LCL).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        // ARG pointer
        ACommand::Reserved(ReservedSymbols::ARG).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        // THIS pointer
        ACommand::Reserved(ReservedSymbols::THIS).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        // THAT pointer
        ACommand::Reserved(ReservedSymbols::THAT).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        // Reposition ARG pointer for callee
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Address(reposition_arg_pointer).into(),
        CCommand::new_dest(CDest::D, CComp::DMinusA).into(),
        ACommand::Reserved(ReservedSymbols::ARG).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Set LCL pointer for callee (first step of callee is to set N lcl args to 0)
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::LCL).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// VM `return` assembly code.
///
/// Can be used by the VM as is.
pub fn return_from_func() -> [Assembly; 35] {
    [
        // LCL is above frame to restore
        ACommand::Reserved(ReservedSymbols::LCL).into(),
        CCommand::new_dest(CDest::D, CComp::MMinusOne).into(),
        ACommand::Reserved(ReservedSymbols::R14).into(),
        // Store topmost frame member in R14
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Restore THAT
        CCommand::new_dest(CDest::A, CComp::D).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::THAT).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Restore THIS
        ACommand::Reserved(ReservedSymbols::R14).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::THIS).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Callee ARG stores where SP was for the caller
        ACommand::Reserved(ReservedSymbols::ARG).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        // +1 because callee always puts one return value on stack
        CCommand::new_dest(CDest::M, CComp::DPlusOne).into(),
        // Restore ARG
        ACommand::Reserved(ReservedSymbols::R14).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::ARG).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Restore LCL
        ACommand::Reserved(ReservedSymbols::R14).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::LCL).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Jump to return address
        ACommand::Reserved(ReservedSymbols::R14).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_jump(CComp::One, CJump::Jump).into(),
    ]
}
