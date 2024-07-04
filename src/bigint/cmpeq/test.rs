use std::str::FromStr;

use crate::bigint::{U255Cmpeq, U510};
use crate::script_loader::AsmScriptLoader;
use crate::traits::comparable::Comparable;
use crate::traits::integer::{NonNativeInteger, NonNativeLimbInteger};
use crate::{debug::print_script_size, treepp::*};
use bitcoin::opcodes::all::OP_EQUALVERIFY;
use num_bigint::{BigUint, RandomBits};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// Tests the validity of asm files
#[test]
fn test_asm_files() {
    let asm_test_files = [
        include_str!("asm_tests/test_1.asm"),
        include_str!("asm_tests/test_2.asm"),
        include_str!("asm_tests/test_3.asm"),
    ];

    for (i, test_file) in asm_test_files.iter().enumerate() {
        println!("testing asm file {:?}...", i);
        let test_script = AsmScriptLoader::from_str(test_file);
        let exec_result = execute_script(test_script);
        assert!(exec_result.success, "test asm file {:?} is wrong!", i);
        println!("asm file {:?} is correct!", i);
    }
}

/// Tests pushing a 255-bit number to the stack. Example taken from the original bitcointalk topic:
/// https://bitcointalk.org/index.php?topic=5477449.0
#[test]
fn test_push_le_slice_255_bits() {
    let example_number = BigUint::from_str("44347314585423944296568073680235476145090606693409235654433373536726375170836");
    let expected_limbs: Vec<u32> = vec![
        25099,
        22628,
        4378,
        17693,
        627,
        25528,
        24377,
        28384,
        14745,
        26534,
        13152,
        27940,
        18633,
        23354,
        13719,
        31767,
        788,
    ];

    let script = script! {
        { U255Cmpeq::OP_PUSH_U32LESLICE(&example_number.unwrap().to_u32_digits()) }
        for limb in expected_limbs.iter().rev() {
            { *limb }
            OP_EQUALVERIFY
        }
        OP_TRUE
    };
    let exec_result = execute_script(script);
    assert!(exec_result.success);
}

// Tests the multiplication of two 254-bit numbers and two 64-bit numbers.
#[test]
fn test_255_bit_cmpeq_widening_mul() {
    const TESTS_NUMBER: usize = 10;

    print_script_size("255-bit widening mul", U255Cmpeq::OP_WIDENINGMUL::<U510>());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        let a: BigUint = prng.sample(RandomBits::new(255));
        let b: BigUint = prng.sample(RandomBits::new(255));
        let c: BigUint = a.clone() * b.clone();

        let script = script! {
            { U255Cmpeq::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U255Cmpeq::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U255Cmpeq::OP_WIDENINGMUL::<U510>() }
            { U510::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U510::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
