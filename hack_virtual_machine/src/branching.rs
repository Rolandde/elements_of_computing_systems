//! Assembly code for VM branching operations.

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

pub fn goto(label: String) -> [Assembly; 2] {
    [
        ACommand::Symbol(label).into(),
        CCommand::new_jump(CComp::One, CJump::Jump).into(),
    ]
}

pub fn if_goto(label: String) -> [Assembly; 6] {
    [
        ACommand::Reserved(ReservedSymbols::SP).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::A, CComp::M).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        ACommand::Symbol(label).into(),
        CCommand::new_jump(CComp::D, CJump::NotEqual).into(),
    ]
}

#[cfg(test)]
mod vm_branching_tests {
    use super::*;

    #[test]
    fn test_goto() {
        let mut vm_goto = goto("label".to_string()).to_vec();
        let goto = [
            ACommand::Address(1).into(),
            ACommand::Address(2).into(),
            ACommand::Address(3).into(),
            Assembly::Label("label".to_string()),
            ACommand::Address(4).into(),
        ];
        vm_goto.extend(goto);
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&vm_goto).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);

        for _ in 0..2 {
            // Goto is 2 assembly commands to get to the jump statement
            d.computer().cycle(false);
        }
        assert_eq!(d.read_cpu_counter(), 5.into());
    }

    #[test]
    fn test_if_goto() {
        let mut vm_goto = if_goto("label".to_string()).to_vec();
        let goto = [
            ACommand::Address(1).into(),
            ACommand::Address(2).into(),
            ACommand::Address(3).into(),
            Assembly::Label("label".to_string()),
            ACommand::Address(4).into(),
        ];
        vm_goto.extend(goto);

        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&vm_goto).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), 257.into());
        d.write_memory(256.into(), 0.into()); // Don't jump
        for _ in 0..6 {
            // if-goto is 6 assembly commands to get to the jump statement
            d.computer().cycle(false);
        }
        assert_eq!(d.read_memory(0.into()), 256.into());
        assert_eq!(d.read_cpu_counter(), 6.into());

        d.computer().cycle(true);
        d.write_memory(0.into(), 257.into());
        d.write_memory(256.into(), 42.into()); // Jump
        for _ in 0..6 {
            // if-goto is 6 assembly commands to get to the jump statement
            d.computer().cycle(false);
        }
        assert_eq!(d.read_memory(0.into()), 256.into());
        assert_eq!(d.read_cpu_counter(), 9.into());
    }
}
