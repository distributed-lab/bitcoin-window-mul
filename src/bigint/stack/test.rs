use crate::bigint::{NonNativeBigIntImpl, U254, U508};
use crate::debug::print_script_size;
use crate::traits::comparable::Comparable;
use crate::traits::integer::NonNativeInteger;
use crate::treepp::{execute_script, pushable};
use bitcoin_script::script;
use num_bigint::{BigUint, RandomBits};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_simple_zip() {
    const N_BITS: usize = 1500;
    const N_U30_LIMBS: u32 = 50;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..50 {
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[i as usize]);
            expected.push(v[(N_U30_LIMBS + i) as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { NonNativeBigIntImpl::<N_BITS, 30>::OP_ZIP(1, 0) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..50 {
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[(N_U30_LIMBS + i) as usize]);
            expected.push(v[i as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { NonNativeBigIntImpl::<N_BITS, 30>::OP_ZIP(0, 1) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the copy operation when performed with the depth of 1.
#[test]
fn test_simple_copy_depth_1() {
    const TESTS_NUMBER: usize = 50;
    const N_U30_LIMBS: usize = 9;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..TESTS_NUMBER {
        // Generating two numbers represented by 9 u32 limbs
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        // We expect to copy the first number
        let expected = &v[0..N_U30_LIMBS];

        // Defining the script
        let script = script! {
            // Push two numbers to the stack
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }

            // Copy the first one (located at the depth of two)
            { U254::OP_PICK(1) }

            // Assert that the copied number is equal to the original
            for i in 0..N_U30_LIMBS {
                { expected[(N_U30_LIMBS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }

            // Dropping both numbers since they are not needed
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the copy operation when performed with the depth of 1
/// using the variable from the stack
#[test]
fn test_simple_copy_depth_1_from_stack() {
    const TESTS_NUMBER: usize = 50;
    const N_U30_LIMBS: usize = 9;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..TESTS_NUMBER {
        // Generating two numbers represented by 9 u32 limbs
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        // We expect to copy the first number
        let expected = &v[0..N_U30_LIMBS];

        // Defining the script for
        let script = script! {
            // Push two numbers to the stack
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }

            // Copy the first one (located at the depth of two)
            { 1 }
            { U254::OP_PICKSTACK() }

            // Assert that the copied number is equal to the original
            for i in 0..N_U30_LIMBS {
                { expected[(N_U30_LIMBS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }

            // Dropping both numbers since they are not needed
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the copy operation when performed with the depth of 0.
#[test]
fn test_simple_copy_depth_0() {
    const TESTS_NUMBER: usize = 50;
    const N_U30_LIMBS: usize = 9;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..TESTS_NUMBER {
        // Generating two numbers represented by 9 u32 limbs
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        // We expect to copy the second number from the stack
        let expected = &v[N_U30_LIMBS..2 * N_U30_LIMBS];

        // Defining the script
        let script = script! {
            // Push two numbers to the stack
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }

            // Copy the second one (located at the top of the stack)
            { U254::OP_PICK(0) }

            // Assert that the copied number is equal to the original
            for i in 0..N_U30_LIMBS {
                { expected[(N_U30_LIMBS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }

            // Dropping both numbers since they are not needed
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the copy operation when performed with the depth of 1
/// using the variable from the stack
#[test]
fn test_simple_copy_depth_1_from_stack_508_bits() {
    const TESTS_NUMBER: usize = 50;
    const N_U30_LIMBS: usize = 17;

    assert_eq!(
        U508::N_LIMBS,
        N_U30_LIMBS,
        "The number of limbs for u508 should be equal to 17"
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..TESTS_NUMBER {
        // Generating two numbers represented by 17 u32 limbs
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        // We expect to copy the first number
        let expected = &v[0..N_U30_LIMBS];

        // Defining the script for
        let script = script! {
            // Push two numbers to the stack
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }

            // Copy the first one (located at the depth of two)
            { 1 }
            { U508::OP_PICKSTACK() }

            // Assert that the copied number is equal to the original
            for i in 0..N_U30_LIMBS {
                { expected[(N_U30_LIMBS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }

            // Dropping both numbers since they are not needed
            { U508::OP_DROP() }
            { U508::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_simple_roll() {
    const N_U30_LIMBS: u32 = 9;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..50 {
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[i as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { U254::OP_ROLL(1) }
            for i in 0..N_U30_LIMBS {
                { expected[(N_U30_LIMBS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_simple_copy_zip() {
    const N_U30_LIMBS: u32 = 9;

    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..50 {
        let mut v = vec![];
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }
        for _ in 0..N_U30_LIMBS {
            v.push(prng.gen::<i32>());
        }

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[i as usize]);
            expected.push(v[(N_U30_LIMBS + i) as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { U254::OP_PICKZIP(1, 0) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[(N_U30_LIMBS + i) as usize]);
            expected.push(v[i as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { U254::OP_PICKZIP(0, 1) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let mut expected = vec![];
        for i in 0..N_U30_LIMBS {
            expected.push(v[i as usize]);
            expected.push(v[i as usize]);
        }

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { U254::OP_PICKZIP(1, 1) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            for i in 0..N_U30_LIMBS * 2 {
                { v[i as usize] }
            }
            { U254::OP_DUPZIP(1) }
            for i in 0..N_U30_LIMBS * 2 {
                { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            { U254::OP_DROP() }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_simple_push_hex() {
    let exec_result = execute_script(script! {
        { U254::OP_PUSH_HEXSTR("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47") }
        410844487 OP_EQUALVERIFY
        813838427 OP_EQUALVERIFY
        119318739 OP_EQUALVERIFY
        542811226 OP_EQUALVERIFY
        22568343 OP_EQUALVERIFY
        18274822 OP_EQUALVERIFY
        436378501 OP_EQUALVERIFY
        329037900 OP_EQUALVERIFY
        12388 OP_EQUAL
    });
    assert!(exec_result.success);
}

#[test]
fn test_composite_push_hex() {
    const LIMBS_NUM: usize = 17;
    assert_eq!(
        LIMBS_NUM,
        U508::N_LIMBS,
        "The number of limbs should be equal to 17"
    );

    let hex_str = "a913493038248cb02c3ca8dc7cd243b10b83617b00aae565d1c445082f89e1031e1a1f4171e9884b388c961d1d7cbbec97b4dd665a3ae1767902e994ddc78b7";
    let limbs: [u32; LIMBS_NUM] = [
        232552631u32,
        507558501,
        440066422,
        517174681,
        399228617,
        589662023,
        696798008,
        679282119,
        504377825,
        289541090,
        627429828,
        99353259,
        990951478,
        924791952,
        808205480,
        14717490,
        177288339,
    ];

    let exec_result = execute_script(script! {
        { U508::OP_PUSH_HEXSTR(hex_str) }
        for i in 0..LIMBS_NUM {
            { limbs[i] }
            OP_EQUALVERIFY
        }

        OP_TRUE
    });
    assert!(exec_result.success);
}

#[test]
/// Tests the extension of 254-bit number to 508-bit number.
fn test_254_bit_widening() {
    print_script_size("254-bit widening", U254::OP_EXTEND::<U508>());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_EXTEND::<U508>() }
            { U508::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U508::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
