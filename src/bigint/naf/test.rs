use crate::bigint::bits::implementation::limb_to_be_bits_toaltstack;
use crate::bigint::naf::implementation::binary_to_be_naf;
use crate::bigint::U254;
use crate::traits::integer::NonNativeInteger;
use crate::{debug::print_script_size, treepp::*};
use ark_ff::{One, Zero};
use num_bigint::{BigInt as NumBigInt, BigUint, RandomBits, ToBigInt};
use num_traits::FromPrimitive;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// Tests the binary-to-naf conversion for a trivial case.
#[test]
fn test_limb_to_naf_trivial() {
    // Launching a script for {0, 1} in binary
    let script = script! {
        { 2 } // {0, 1} in binary
        { limb_to_be_bits_toaltstack(2) }
        { binary_to_be_naf(2) }
        0 OP_EQUALVERIFY
        1 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "trivial case (0, 1) failed");

    // Launching a script for {1, 1} in binary
    let script = script! {
        { 3 } // {1, 1} in binary
        { limb_to_be_bits_toaltstack(2) }
        { binary_to_be_naf(2) }
        1 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        -1 OP_EQUALVERIFY
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "trivial case (1, 1) failed");

    // Launching a script for {1, 1, 1} in binary
    let script = script! {
        { 7 } // {1, 1, 1} in binary
        { limb_to_be_bits_toaltstack(3) }
        { binary_to_be_naf(3) }
        // Should get {-1, 0, 0, 1}
        1 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        -1 OP_EQUALVERIFY
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "trivial case (1, 1, 1) failed");

    // Launching a script for {0, 1, 1, 1} in binary
    let script = script! {
        { 14 } // {0, 1, 1, 1} in binary
        { limb_to_be_bits_toaltstack(5) }
        { binary_to_be_naf(4) }
        // Should get {0, -1, 0, 0, 1}
        1 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        -1 OP_EQUALVERIFY
        0 OP_EQUALVERIFY
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "trivial case (0, 1, 1, 1) failed");
}

/// Tests the binary-to-naf conversion for random case
#[test]
fn test_limb_to_naf() {
    /// Number of bits for the single limb
    const BITS_NUM: usize = 30;
    /// Number of tests to generate
    const TESTS_NUM: usize = 100;

    print_script_size("binary_to_naf", binary_to_be_naf(BITS_NUM));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        // Picking a random number
        let test_number: u32 = prng.gen_range(0..1 << BITS_NUM as u32);

        // Decomposing a number into wnaf representation
        let mut wnaf_decomposition = {
            let mut decomposition = vec![];
            let mut k = test_number.clone();

            while k >= 1 {
                if k % 2 == 1 {
                    let c: i32 = 2 - (k % 4) as i32;
                    decomposition.push(c);
                    k = (k as i32 - c) as u32;
                } else {
                    decomposition.push(0i32);
                }

                k = k / 2;
            }

            decomposition
        };

        wnaf_decomposition.resize(BITS_NUM + 1, 0);
        assert_eq!(
            wnaf_decomposition.len(),
            BITS_NUM + 1,
            "wnaf decomposition has incorrect length"
        );

        // Verifying that the decomposition was done correctly
        let from_wnaf_value = wnaf_decomposition
            .iter()
            .enumerate()
            .fold(0, |acc, (i, c)| acc + c * 2i32.pow(i as u32));
        assert_eq!(
            test_number as i32, from_wnaf_value,
            "wnaf decomposition was done incorrectly"
        );

        // Launching a script
        let script = script! {
            { test_number }
            { limb_to_be_bits_toaltstack(BITS_NUM) }
            { binary_to_be_naf(BITS_NUM) }
            for coefficient in wnaf_decomposition.iter().rev() {
                { *coefficient }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the conversion of a big integer to wnaf representation
#[test]
fn test_bigint_to_naf() {
    const TESTS_NUM: usize = 10;

    print_script_size("u254_to_wnaf", U254::convert_to_be_naf_bits());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let test_number: BigUint = prng.sample(RandomBits::new(254));

        // Decomposing a number into wnaf representation
        let mut wnaf_decomposition = {
            let mut decomposition = vec![];
            let mut k = test_number.to_bigint().unwrap();

            while k.ge(&NumBigInt::one()) {
                let modulo_2: NumBigInt = k.clone() % 2;

                let modulo_4: NumBigInt = k.clone() % 4;
                let (_, modulo_4) = modulo_4.to_u32_digits();
                let modulo_4 = {
                    if modulo_4.len() == 0 {
                        0
                    } else {
                        modulo_4[0]
                    }
                };

                if modulo_2.eq(&NumBigInt::one()) {
                    let c: i32 = 2 - modulo_4 as i32;
                    decomposition.push(c);
                    k = k.checked_sub(&NumBigInt::from_i32(c).unwrap()).unwrap();
                } else {
                    decomposition.push(0i32);
                }

                k = k / 2;
            }

            decomposition
        };

        // Verifying that the decomposition was done correctly
        let from_wnaf_value =
            wnaf_decomposition
                .iter()
                .enumerate()
                .fold(NumBigInt::zero(), |acc, (i, c)| {
                    let addition =
                        c.to_bigint().unwrap() * NumBigInt::pow(&2.to_bigint().unwrap(), i as u32);
                    acc + addition
                });
        assert_eq!(
            test_number,
            from_wnaf_value.to_biguint().unwrap(),
            "wnaf decomposition was done incorrectly"
        );

        wnaf_decomposition.resize(255, 0);
        assert_eq!(
            wnaf_decomposition.len(),
            255,
            "wnaf decomposition has incorrect length"
        );

        // Launching a script
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&test_number.to_u32_digits()) }
            { U254::convert_to_be_naf_bits() }
            for coefficient in wnaf_decomposition.iter().rev() {
                { *coefficient }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the conversion of a big integer to wnaf representation and
/// additionally pushed to the alt stack.
#[test]
fn test_bigint_to_naf_altstack() {
    const TESTS_NUM: usize = 10;

    print_script_size(
        "u254_to_wnaf_altstack",
        U254::convert_to_be_naf_bits_toaltstack(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let test_number: BigUint = prng.sample(RandomBits::new(254));

        // Decomposing a number into wnaf representation
        let mut wnaf_decomposition = {
            let mut decomposition = vec![];
            let mut k = test_number.to_bigint().unwrap();

            while k.ge(&NumBigInt::one()) {
                let modulo_2: NumBigInt = k.clone() % 2;

                let modulo_4: NumBigInt = k.clone() % 4;
                let (_, modulo_4) = modulo_4.to_u32_digits();
                let modulo_4 = {
                    if modulo_4.len() == 0 {
                        0
                    } else {
                        modulo_4[0]
                    }
                };

                if modulo_2.eq(&NumBigInt::one()) {
                    let c: i32 = 2 - modulo_4 as i32;
                    decomposition.push(c);
                    k = k.checked_sub(&NumBigInt::from_i32(c).unwrap()).unwrap();
                } else {
                    decomposition.push(0i32);
                }

                k = k / 2;
            }

            decomposition
        };

        // Verifying that the decomposition was done correctly
        let from_wnaf_value =
            wnaf_decomposition
                .iter()
                .enumerate()
                .fold(NumBigInt::zero(), |acc, (i, c)| {
                    let addition =
                        c.to_bigint().unwrap() * NumBigInt::pow(&2.to_bigint().unwrap(), i as u32);
                    acc + addition
                });
        assert_eq!(
            test_number,
            from_wnaf_value.to_biguint().unwrap(),
            "wnaf decomposition was done incorrectly"
        );

        wnaf_decomposition.resize(255, 0);
        assert_eq!(
            wnaf_decomposition.len(),
            255,
            "wnaf decomposition has incorrect length"
        );

        // Launching a script
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&test_number.to_u32_digits()) }
            { U254::convert_to_be_naf_bits_toaltstack() }
            for coefficient in wnaf_decomposition {
                OP_FROMALTSTACK
                { coefficient }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
