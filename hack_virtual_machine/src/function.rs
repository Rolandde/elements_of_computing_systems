//! Assembly code for VM function calls.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Standalone assembly block that initializes local variables on the stack to 0.
///
/// Assumes the number of vars is in the D register.
pub fn local_vars() -> [Assembly; 12] {
    [
        Assembly::Label("LOCAL_VARS".to_string()),
        CCommand::new_dest(CDest::D, CComp::DMinusOne).into(),
        ACommand::Symbol("LOCAL_END".to_string()).into(),
        CCommand::new_jump(CComp::D, CJump::Less).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::M, CComp::Zero).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
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
pub fn call_stack(n_args: i16) -> [Assembly; 38] {
    // Args for callee are pushed on the stack before this call.
    // The ARG pointer for callee has to be set after the ARG pointer for the caller function has been stored
    // 4 comes from 5 values being pushed on the stack, but the assembly logic always going one back after a push
    let reposition_arg_pointer = 4 + n_args;
    [
        // Return address
        CCommand::new_dest(CDest::D, CComp::A).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // LCL pointer
        ACommand::Reserved(ReservedSymbols::LCL).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // ARG pointer
        ACommand::Reserved(ReservedSymbols::ARG).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // THIS pointer
        ACommand::Reserved(ReservedSymbols::THIS).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // THAT pointer
        ACommand::Reserved(ReservedSymbols::THAT).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
        // Reposition ARG pointer for callee
        CCommand::new_dest(CDest::D, CComp::A).into(),
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
pub fn return_from_func() -> [Assembly; 34] {
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

#[cfg(test)]
mod vm_function_tests {
    use super::*;

    #[test]
    fn test_local() {
        let mut vm_goto = local_vars().to_vec();
        vm_goto.push(ACommand::Address(0).into()); // `local_vars` ends on a label and that's not allowed
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&vm_goto).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 256.into());
        d.write_memory(256.into(), 41.into());
        d.write_memory(257.into(), 42.into());
        d.write_memory(258.into(), 43.into());
        d.write_register_d(0.into()); // Add no local vars

        while d.read_cpu_counter() != 10.into() {
            d.computer().cycle(false);
        }

        assert_eq!(d.read_memory(0.into()), 256.into());
        assert_eq!(d.read_memory(256.into()), 41.into());
        assert_eq!(d.read_memory(257.into()), 42.into());
        assert_eq!(d.read_memory(258.into()), 43.into());

        d.computer().cycle(true);
        d.write_register_d(2.into()); // 2 local vars

        while d.read_cpu_counter() != 10.into() {
            d.computer().cycle(false);
        }

        assert_eq!(d.read_memory(0.into()), 258.into());
        assert_eq!(d.read_memory(256.into()), 0.into());
        assert_eq!(d.read_memory(257.into()), 0.into());
        assert_eq!(d.read_memory(258.into()), 43.into());
    }

    #[test]
    fn test_call_stack() {
        let vm_goto = call_stack(3).to_vec();
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&vm_goto).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 403.into()); // 3 arg on the stack already. The ARG will point to 400.
        d.write_memory(ReservedSymbols::LCL.into(), 350.into());
        d.write_memory(ReservedSymbols::ARG.into(), 345.into());
        d.write_memory(ReservedSymbols::THIS.into(), 3000.into());
        d.write_memory(ReservedSymbols::THAT.into(), 4000.into());
        d.write_register_a(512.into()); // Return address expected on A register

        let i = i16::try_from(vm_goto.len()).unwrap();
        while d.read_cpu_counter() != i.into() {
            d.computer().cycle(false);
        }

        assert_eq!(d.read_memory(0.into()), 408.into());
        assert_eq!(d.read_memory(403.into()), 512.into());
        assert_eq!(d.read_memory(404.into()), 350.into());
        assert_eq!(d.read_memory(405.into()), 345.into());
        assert_eq!(d.read_memory(406.into()), 3000.into());
        assert_eq!(d.read_memory(407.into()), 4000.into());
        assert_eq!(d.read_memory(ReservedSymbols::ARG.into()), 400.into());
        assert_eq!(d.read_memory(ReservedSymbols::LCL.into()), 408.into());
    }

    #[test]
    fn test_return() {
        let vm_goto = return_from_func().to_vec();
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&vm_goto).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(ReservedSymbols::LCL.into(), 400.into()); // LCL points to the top of the frame
        d.write_memory(399.into(), 4000.into());
        d.write_memory(398.into(), 3000.into());
        d.write_memory(397.into(), 350.into());
        d.write_memory(396.into(), 360.into());
        d.write_memory(395.into(), 10000.into());
        d.write_memory(ReservedSymbols::ARG.into(), 380.into());

        for _ in 0..vm_goto.len() {
            d.computer().cycle(false);
        }

        assert_eq!(d.read_memory(ReservedSymbols::THAT.into()), 4000.into());
        assert_eq!(d.read_memory(ReservedSymbols::THIS.into()), 3000.into());
        assert_eq!(d.read_memory(ReservedSymbols::ARG.into()), 350.into());
        assert_eq!(d.read_memory(ReservedSymbols::LCL.into()), 360.into());
        // ARG pointer marks the stack pointer the function being returned to (that put the args there in the first place)
        // +1 because the function returning always puts on return value on top of stack
        assert_eq!(d.read_memory(0.into()), 381.into());
        assert_eq!(d.read_cpu_counter(), 10000.into());
    }
}
