use crate::bigint::{NonNativeBigIntImpl, U254};
use crate::traits::integer::NonNativeInteger;
use crate::treepp::{execute_script, pushable};
use bitcoin_script::script;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_zip() {
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
fn test_copy_depth_1() {
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
fn test_copy_depth_1_from_stack() {
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
fn test_copy_depth_0() {
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

#[test]
fn test_roll() {
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
fn test_copy_zip() {
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
fn push_hex() {
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
