use std::convert::Into;

use hack_assembler::parts::{ACommand, CCommand, CComp, CDest, CJump, ReservedSymbols};
use hack_assembler::Assembly;

/// Virtual machine stack addition.
pub fn add() -> [Assembly; 8] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::DPlusM).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack subtraction.
pub fn sub() -> [Assembly; 8] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack negation.
pub fn neg() -> [Assembly; 3] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::MinusM).into(),
    ]
}

/// Virtual machine stack equality
pub fn eq() -> [Assembly; 24] {
    // For the comments, assume stack pointer at memory 0 points to 3
    // The two numbers to compare at memory 1(X) and 2(Y)
    [
        ReservedSymbols::SP.into(), // A = 0 (stack pointer)
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(), // A = M[0] - 1 = 3 - 1 = 2 (top of stack)
        CCommand::new_dest(CDest::D, CComp::M).into(),         // D = M[2] = Y
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(), // A = 1
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(),   // M[1] = X - Y
        CCommand::new_dest(CDest::D, CComp::A).into(),         // D = 1
        ReservedSymbols::SP.into(),                            // A = 0
        CCommand::new_dest(CDest::M, CComp::D).into(), // M[0] = 1, stack pointer is at subtraction result
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1
        CCommand::new_dest(CDest::D, CComp::M).into(), // D = M[1] = X - Y
        ACommand::Symbol("EQ_TRUE".to_string()).into(), // Label to jump to if equal
        CCommand::new_jump(CComp::D, CJump::Equal).into(), // Jump to EQUAL if D is 0, otherwise not equal
        ReservedSymbols::SP.into(),                        // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1 (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::Zero).into(), // M[1] = 0
        ACommand::Symbol("EQ_DONE".to_string()).into(), // Jump to finishing equal assembly
        CCommand::new_jump(CComp::Zero, CJump::Jump).into(), // Always jump to finishing assembly
        Assembly::Label("EQ_TRUE".to_string()),        // Start of code for equality
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1, (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::MinumOne).into(), // M[1] = -1 (true, X and Y are equal)
        Assembly::Label("EQ_DONE".to_string()),        // Code for finishing up equality
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(), // M[0] = M[0] + 1 = 1 + 1 = 2
    ]
}

/// Virtual machine stack greater than
pub fn gt() -> [Assembly; 24] {
    // For the comments, assume stack pointer at memory 0 points to 3
    // The two numbers to compare at memory 1(X) and 2(Y)
    [
        ReservedSymbols::SP.into(), // A = 0 (stack pointer)
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(), // A = M[0] - 1 = 3 - 1 = 2 (top of stack)
        CCommand::new_dest(CDest::D, CComp::M).into(),         // D = M[2] = Y
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(), // A = 1
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(),   // M[1] = X - Y
        CCommand::new_dest(CDest::D, CComp::A).into(),         // D = 1
        ReservedSymbols::SP.into(),                            // A = 0
        CCommand::new_dest(CDest::M, CComp::D).into(), // M[0] = 1, stack pointer is at subtraction result
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1
        CCommand::new_dest(CDest::D, CComp::M).into(), // D = M[1] = X - Y
        ACommand::Symbol("GT_TRUE".to_string()).into(), // Label to jump to if greater than
        CCommand::new_jump(CComp::D, CJump::Greater).into(), // Jump if D is greater than 0, otherwise not greater than
        ReservedSymbols::SP.into(),                          // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1 (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::Zero).into(), // M[1] = 0
        ACommand::Symbol("GT_DONE".to_string()).into(), // Jump to setting stack pointer
        CCommand::new_jump(CComp::Zero, CJump::Jump).into(), // Always jump to finishing assembly
        Assembly::Label("GT_TRUE".to_string()),        // Start of code for greater than being true
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1, (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::MinumOne).into(), // M[1] = -1 (true, X and Y are equal)
        Assembly::Label("GT_DONE".to_string()),        // Code for setting stack pointer
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(), // M[0] = M[0] + 1 = 1 + 1 = 2
    ]
}

/// Virtual machine stack less than
pub fn lt() -> [Assembly; 24] {
    // For the comments, assume stack pointer at memory 0 points to 3
    // The two numbers to compare at memory 1(X) and 2(Y)
    [
        ReservedSymbols::SP.into(), // A = 0 (stack pointer)
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(), // A = M[0] - 1 = 3 - 1 = 2 (top of stack)
        CCommand::new_dest(CDest::D, CComp::M).into(),         // D = M[2] = Y
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(), // A = 1
        CCommand::new_dest(CDest::M, CComp::MMinusD).into(),   // M[1] = X - Y
        CCommand::new_dest(CDest::D, CComp::A).into(),         // D = 1
        ReservedSymbols::SP.into(),                            // A = 0
        CCommand::new_dest(CDest::M, CComp::D).into(), // M[0] = 1, stack pointer is at subtraction result
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1
        CCommand::new_dest(CDest::D, CComp::M).into(), // D = M[1] = X - Y
        ACommand::Symbol("LT_TRUE".to_string()).into(), // Label to jump to if less than
        CCommand::new_jump(CComp::D, CJump::Less).into(), // Jump if D is less than 0, otherwise not less than
        ReservedSymbols::SP.into(),                       // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1 (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::Zero).into(), // M[1] = 0
        ACommand::Symbol("LT_DONE".to_string()).into(), // Jump to setting stack pointer
        CCommand::new_jump(CComp::Zero, CJump::Jump).into(), // Always jump to finishing assembly
        Assembly::Label("LT_TRUE".to_string()),        // Start of code for greater than being true
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::A, CComp::M).into(), // A = M[0] = 1, (address where true/false needs to be written)
        CCommand::new_dest(CDest::M, CComp::MinumOne).into(), // M[1] = -1 (true, X and Y are equal)
        Assembly::Label("LT_DONE".to_string()),        // Code for setting stack pointer
        ReservedSymbols::SP.into(),                    // A = 0
        CCommand::new_dest(CDest::M, CComp::MPlusOne).into(), // M[0] = M[0] + 1 = 1 + 1 = 2
    ]
}

/// Virtual machine stack bitwise and.
pub fn and() -> [Assembly; 8] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::DAndM).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack bitwise or.
pub fn or() -> [Assembly; 8] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::D, CComp::M).into(),
        CCommand::new_dest(CDest::A, CComp::AMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::DOrM).into(),
        CCommand::new_dest(CDest::D, CComp::APlusOne).into(),
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::M, CComp::D).into(),
    ]
}

/// Virtual machine stack bitwise not
pub fn not() -> [Assembly; 3] {
    [
        ReservedSymbols::SP.into(),
        CCommand::new_dest(CDest::A, CComp::MMinusOne).into(),
        CCommand::new_dest(CDest::M, CComp::NotM).into(),
    ]
}

#[cfg(test)]
mod vm_arithmetic_tests {
    use super::*;
    use std::convert::TryFrom;

    // Memory address and the expected value. Converted into a assert_eq!.
    struct MemVal(i16, i16);

    // Stack testing follows the same receipe
    fn stack_test(
        ass: &[Assembly],          // The assembly to test
        stack_pointer: i16,        // Where is the stack pointer
        top_value: i16,            // What value is at the top of the stack
        bottom_value: Option<i16>, // What's the next value in the stack. Empty for unary operations
        assert: Vec<MemVal>,       // Expected values and their memory addresses
    ) {
        let mut rom = hack_interface::RomWriter::new();
        for i in hack_assembler::assemble_from_slice(&ass).unwrap() {
            rom.write_instruction(i);
        }
        let mut c = rom.create_load_rom();
        let mut d = hack_interface::Debugger::new(&mut c);
        d.write_memory(0.into(), stack_pointer.into());
        let mut stack = stack_pointer - 1;
        d.write_memory(stack.into(), top_value.into());
        stack -= 1;
        match bottom_value {
            Some(b) => d.write_memory(stack.into(), b.into()),
            None => {}
        };
        let i = i16::try_from(ass.len()).unwrap();
        while d.read_cpu_counter() != i.into() {
            d.computer().cycle(false);
        }

        for asrt in assert {
            assert_eq!(d.read_memory(asrt.0.into()), asrt.1.into())
        }
    }

    #[test]
    fn test_add() {
        stack_test(
            &add(),
            456,
            100,
            Some(10),
            vec![MemVal(454, 110), MemVal(0, 455)],
        )
    }

    #[test]
    fn test_add_neg() {
        stack_test(
            &add(),
            260,
            -100,
            Some(10),
            vec![MemVal(258, -90), MemVal(0, 259)],
        )
    }

    #[test]
    fn test_sub() {
        stack_test(&sub(), 3, 100, Some(10), vec![MemVal(1, -90), MemVal(0, 2)])
    }

    #[test]
    fn test_sub_double_neg() {
        stack_test(
            &sub(),
            3,
            -100,
            Some(10),
            vec![MemVal(1, 110), MemVal(0, 2)],
        )
    }

    #[test]
    fn test_neg() {
        stack_test(
            &neg(),
            456,
            100,
            None,
            vec![MemVal(455, -100), MemVal(0, 456)],
        )
    }

    #[test]
    fn test_neg_neg() {
        stack_test(
            &neg(),
            456,
            -100,
            None,
            vec![MemVal(455, 100), MemVal(0, 456)],
        )
    }

    #[test]
    fn test_eq() {
        stack_test(
            &eq(),
            3,
            -100,
            Some(-100),
            vec![MemVal(1, -1), MemVal(0, 2)],
        )
    }

    #[test]
    fn test_eq_false() {
        stack_test(&eq(), 3, -100, Some(100), vec![MemVal(1, 0), MemVal(0, 2)])
    }

    #[test]
    fn test_gt() {
        stack_test(&gt(), 3, -100, Some(-99), vec![MemVal(1, -1), MemVal(0, 2)])
    }

    #[test]
    fn test_gt_false_eq() {
        stack_test(&gt(), 3, 1, Some(1), vec![MemVal(1, 0), MemVal(0, 2)])
    }

    #[test]
    fn test_gt_false_less() {
        stack_test(&gt(), 3, 10, Some(1), vec![MemVal(1, 0), MemVal(0, 2)])
    }

    #[test]
    fn test_lt() {
        stack_test(&lt(), 3, -1, Some(-2), vec![MemVal(1, -1), MemVal(0, 2)])
    }

    #[test]
    fn test_lt_false_eq() {
        stack_test(&lt(), 3, 1, Some(1), vec![MemVal(1, 0), MemVal(0, 2)])
    }

    #[test]
    fn test_lt_false_greater() {
        stack_test(&lt(), 3, 1, Some(10), vec![MemVal(1, 0), MemVal(0, 2)])
    }

    #[test]
    fn test_and() {
        stack_test(&and(), 3, 0, Some(0), vec![MemVal(1, 0), MemVal(0, 2)]);
        stack_test(&and(), 3, -1, Some(0), vec![MemVal(1, 0), MemVal(0, 2)]);
        stack_test(&and(), 3, -1, Some(-1), vec![MemVal(1, -1), MemVal(0, 2)]);
        stack_test(&and(), 3, 57, Some(28), vec![MemVal(1, 24), MemVal(0, 2)]);
    }

    #[test]
    fn test_or() {
        stack_test(&or(), 3, 0, Some(0), vec![MemVal(1, 0), MemVal(0, 2)]);
        stack_test(&or(), 3, -1, Some(0), vec![MemVal(1, -1), MemVal(0, 2)]);
        stack_test(&or(), 3, -1, Some(-1), vec![MemVal(1, -1), MemVal(0, 2)]);
    }

    #[test]
    fn test_not() {
        stack_test(&not(), 3, 0, None, vec![MemVal(2, -1), MemVal(0, 3)]);
        stack_test(&not(), 3, -1, None, vec![MemVal(2, 0), MemVal(0, 3)]);
    }
}
