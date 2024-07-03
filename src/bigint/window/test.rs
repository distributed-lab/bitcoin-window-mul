use crate::bigint::bits::implementation::limb_to_be_bits_toaltstack;
use crate::bigint::window::precompute::WindowedPrecomputeTable;
use crate::bigint::window::{binary_to_windowed_form_toaltstack, NonNativeWindowedBigIntImpl};
use crate::bigint::U254;
use crate::traits::comparable::Comparable;
use crate::traits::integer::NonNativeInteger;
use crate::traits::window::Windowable;
use crate::{debug::print_script_size, treepp::*};
use ark_ff::{One, Zero};
use num_bigint::{BigInt, BigUint, RandomBits, ToBigInt, ToBigUint};
use num_traits::FromPrimitive;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_30bit_limb_to_3_width_form() {
    /// The number of tests to conduct
    const LIMB_BIT_SIZE: usize = 30;
    const WINDOW_WIDTH: usize = 3;
    const TESTS_NUM: usize = 30;

    for _ in 0..TESTS_NUM {
        // Picking a random 30-bit number
        let limb: u32 = rand::random::<u32>() % (1 << LIMB_BIT_SIZE);

        // Decomposing into the 3-width form
        let mut decomposition = vec![];
        let mut k = limb.clone();

        while k >= 1 {
            let c = k % (1 << WINDOW_WIDTH);
            decomposition.push(c);
            k = k - c;
            k = k / (1 << WINDOW_WIDTH);
        }

        // Asserting that decomposition is indeed correct
        let from_decomposition = decomposition
            .iter()
            .enumerate()
            .fold(0, |acc, (i, c)| acc + c * (1 << (WINDOW_WIDTH * i)));
        assert_eq!(
            limb, from_decomposition,
            "decomposition was done incorrectly"
        );

        let script = script! {
            { limb } // 30-bit number
            { limb_to_be_bits_toaltstack(LIMB_BIT_SIZE) }
            { binary_to_windowed_form_toaltstack::<WINDOW_WIDTH>(LIMB_BIT_SIZE) }

            for coefficient in decomposition {
                OP_FROMALTSTACK
                { coefficient }
                OP_EQUALVERIFY
            }

            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "30-bit limb to 3-width form failed");
    }
}

#[test]
fn test_23bit_limb_to_4_width_form() {
    /// The number of tests to conduct
    const LIMB_BIT_SIZE: usize = 23;
    const WINDOW_WIDTH: usize = 4;
    const TESTS_NUM: usize = 30;

    for _ in 0..TESTS_NUM {
        // Picking a random 30-bit number
        let limb: u32 = rand::random::<u32>() % (1 << LIMB_BIT_SIZE);

        // Decomposing into the 3-width form
        let mut decomposition = vec![];
        let mut k = limb.clone();

        while k >= 1 {
            let c = k % (1 << WINDOW_WIDTH);
            decomposition.push(c);
            k = k - c;
            k = k / (1 << WINDOW_WIDTH);
        }

        // Asserting that decomposition is indeed correct
        let from_decomposition = decomposition
            .iter()
            .enumerate()
            .fold(0, |acc, (i, c)| acc + c * (1 << (WINDOW_WIDTH * i)));
        assert_eq!(
            limb, from_decomposition,
            "decomposition was done incorrectly"
        );

        let script = script! {
            { limb } // 30-bit number
            { limb_to_be_bits_toaltstack(LIMB_BIT_SIZE) }
            { binary_to_windowed_form_toaltstack::<WINDOW_WIDTH>(LIMB_BIT_SIZE) }

            for coefficient in decomposition {
                OP_FROMALTSTACK
                { coefficient }
                OP_EQUALVERIFY
            }

            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "30-bit limb to 3-width form failed");
    }
}

#[test]
fn test_254_bit_to_w_width() {
    /// The number of tests to conduct
    const TESTS_NUM: usize = 30;
    const WINDOW_WIDTH: usize = 3;

    type U254Windowed = NonNativeWindowedBigIntImpl<U254, WINDOW_WIDTH>;

    print_script_size(
        "u254_to_3_width_form",
        U254Windowed::OP_TOLEWINDOWEDFORM_TOALTSTACK(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let test_number: BigUint = prng.sample(RandomBits::new(254));

        // Decomposing a number into wnaf representation
        let mut decomposition = {
            let mut decomposition = vec![];
            let mut k = test_number.clone();
            let window_size = (1 << WINDOW_WIDTH).to_biguint().unwrap();

            while k.ge(&BigUint::one()) {
                // TODO: I do not know what I am doing with so many clones, so FIXME later please
                let c: BigUint = k.clone() % window_size.clone();
                decomposition.push(c.clone());
                k = k - c;
                k = k / window_size.clone();
            }

            decomposition
        };

        // Verifying that the decomposition was done correctly
        let from_decomposition =
            decomposition
                .iter()
                .enumerate()
                .fold(BigInt::zero(), |acc, (i, c)| {
                    let power_of_two = BigInt::from_u8(2u8).unwrap().pow((WINDOW_WIDTH * i) as u32);
                    acc + c.to_bigint().unwrap() * power_of_two
                });
        assert_eq!(
            test_number,
            from_decomposition.to_biguint().unwrap(),
            "w-width decomposition was done incorrectly"
        );

        decomposition.resize(254 / WINDOW_WIDTH + 1, 0.to_biguint().unwrap());
        assert_eq!(
            decomposition.len(),
            254 / WINDOW_WIDTH + 1,
            "w-width decomposition has incorrect length"
        );

        // Converting to u32 array
        let decomposition = decomposition
            .iter()
            .map(|c| {
                let digits = c.to_u32_digits();
                assert!(digits.len() <= 1, "big integer has more than one digit");
                if digits.len() == 0 {
                    0
                } else {
                    digits[0]
                }
            })
            .collect::<Vec<_>>();

        // Launching a script in le order
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&test_number.to_u32_digits()) }
            { U254Windowed::OP_TOLEWINDOWEDFORM_TOALTSTACK() }
            for coefficient in decomposition.iter() {
                OP_FROMALTSTACK
                { *coefficient }
                OP_EQUALVERIFY
            }

            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "le w-width form failed");

        // Launching a script in be order
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&test_number.to_u32_digits()) }
            { U254Windowed::OP_TOBEWINDOWEDFORM_TOALTSTACK() }
            for coefficient in decomposition.iter().rev() {
                OP_FROMALTSTACK
                { *coefficient }
                OP_EQUALVERIFY
            }

            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "be w-width form failed");
    }
}

#[test]
fn test_mul_width_3_precompute() {
    print_script_size(
        "254-bit 3-width precompute",
        WindowedPrecomputeTable::<U254, 3>::initialize(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    let a: BigUint = prng.sample(RandomBits::new(254));

    let expected_precomputed_values = {
        let mut precomputed_values: Vec<BigUint> = vec![];
        for i in 0..1 << 3 {
            precomputed_values.push(i.to_biguint().unwrap() * a.clone());
        }

        precomputed_values
    };

    assert_eq!(
        expected_precomputed_values.len(),
        1 << 3,
        "precomputed values are incorrect"
    );
    assert_eq!(
        *expected_precomputed_values.first().unwrap(),
        0.to_biguint().unwrap(),
        "precomputed values are incorrect"
    );
    assert_eq!(
        *expected_precomputed_values.last().unwrap(),
        a.clone() * 7u32,
        "precomputed values are incorrect"
    );

    let script = script! {
        { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
        { WindowedPrecomputeTable::<U254, 3>::initialize() }
        for expected_value in expected_precomputed_values.iter().rev() {
            { U254::OP_PUSH_U32LESLICE(&expected_value.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
        }
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "3-width precompute test failed");
}

#[test]
fn test_lazy_mul_width_w_precompute() {
    const WIDTH: usize = 4;
    print_script_size(
        format!("254-bit {:?}-width lazy precompute", WIDTH).as_str(),
        WindowedPrecomputeTable::<U254, 3>::lazy_initialize(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    let a: BigUint = prng.sample(RandomBits::new(254));

    let expected_precomputed_values = {
        let mut precomputed_values: Vec<BigUint> = vec![];
        for i in 0..1 << WIDTH {
            precomputed_values.push(i.to_biguint().unwrap() * a.clone());
        }

        precomputed_values
    };

    assert_eq!(
        expected_precomputed_values.len(),
        1 << WIDTH,
        "precomputed values are incorrect"
    );
    assert_eq!(
        *expected_precomputed_values.first().unwrap(),
        0.to_biguint().unwrap(),
        "precomputed values are incorrect"
    );
    assert_eq!(
        *expected_precomputed_values.last().unwrap(),
        a.clone() * ((1 << WIDTH) - 1).to_biguint().unwrap(),
        "precomputed values are incorrect"
    );

    let script = script! {
        { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
        { WindowedPrecomputeTable::<U254, WIDTH>::lazy_initialize() }
        for expected_value in expected_precomputed_values.iter().rev() {
            { U254::OP_PUSH_U32LESLICE(&expected_value.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
        }
        OP_TRUE
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success, "lazy precompute test failed");
}