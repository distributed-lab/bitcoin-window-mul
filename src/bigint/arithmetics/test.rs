use crate::bigint::arithmetics::add::{limb_add_carry, limb_sub_carry};
use crate::bigint::window::NonNativeWindowedBigIntImpl;
use crate::bigint::{U254Windowed, U254, U508, U64};
use crate::traits::arithmeticable::Arithmeticable;
use crate::traits::comparable::Comparable;
use crate::traits::integer::{NonNativeInteger, NonNativeLimbInteger};
use crate::{debug::print_script_size, treepp::*};
use core::ops::{Add, Mul, Rem, Shl};
use num_bigint::{BigUint, RandomBits, ToBigUint};
use num_traits::One;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_64_and_254_bit_add() {
    print_script_size("254_bit_add", U254::OP_ADD(1, 0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (a.clone() + b.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_ADD(1, 0) }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: u64 = prng.gen();
        let b: u64 = prng.gen();
        let c = a.wrapping_add(b);

        let script = script! {
            { U64::OP_PUSH_U64LESLICE(&[a]) }
            { U64::OP_PUSH_U64LESLICE(&[b]) }
            { U64::OP_ADD(1, 0) }
            { U64::OP_PUSH_U64LESLICE(&[c]) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_508_bit_add() {
    const TESTS_NUMBER: usize = 100;

    print_script_size("508_bit_add", U508::OP_ADD(1, 0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        let a: BigUint = prng.sample(RandomBits::new(507));
        let b: BigUint = prng.sample(RandomBits::new(507));
        let c: BigUint = a.clone() + b.clone();

        let script = script! {
            { U508::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U508::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U508::OP_ADD(1, 0) }
            { U508::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U508::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_254_bit_sub() {
    print_script_size("254_bit_sub", U254::OP_SUB(1, 0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let mut a: BigUint = prng.sample(RandomBits::new(254));
        let mut b: BigUint = prng.sample(RandomBits::new(254));
        if b > a {
            std::mem::swap(&mut a, &mut b);
        }
        let c: BigUint = (a.clone() - b.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_SUB(1, 0) }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_64_and_254_bit_double() {
    print_script_size("u254_double", U254::OP_2MUL(0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (a.clone() + a.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_2MUL(0) }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: u64 = prng.gen();
        let c = a.wrapping_add(a);

        let script = script! {
            { U64::OP_PUSH_U64LESLICE(&[a]) }
            { U64::OP_2MUL(0) }
            { U64::OP_PUSH_U64LESLICE(&[c]) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_16_mul() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (16.to_biguint().unwrap() * a.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_2MUL(0) }
            { U254::OP_2MUL(0) }
            { U254::OP_2MUL(0) }
            { U254::OP_2MUL(0) }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: u64 = prng.gen();
        let c = a.wrapping_add(a);

        let script = script! {
            { U64::OP_PUSH_U64LESLICE(&[a]) }
            { U64::OP_2MUL(0) }
            { U64::OP_PUSH_U64LESLICE(&[c]) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_64_and_256_bit_2mul() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (256.to_biguint().unwrap() * a.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            for _ in 0..8 {
                { U254::OP_2MUL(0) }
            }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: u64 = prng.gen();
        let c = a.wrapping_add(a);

        let script = script! {
            { U64::OP_PUSH_U64LESLICE(&[a]) }
            { U64::OP_2MUL(0) }
            { U64::OP_PUSH_U64LESLICE(&[c]) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the `limb_add_carry` method for adding two limbs.
///
/// It generates random 30-bit limbs and initializes a base of 2^30 and
/// then verifies the correctness of the output.
#[test]
fn test_limb_add_carry() {
    const BASE: u32 = 1 << 30;
    const TESTS_NUMBER: usize = 50;

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        // Generate two limbs
        let limb_1: u32 = prng.gen_range(0..1 << 30);
        let limb_2: u32 = prng.gen_range(0..1 << 30);

        let expected_carry = (limb_1 + limb_2 >= BASE) as u32;
        let expected_sum = limb_1 + limb_2 - expected_carry * BASE;

        let script = script! {
            { limb_1 }
            { limb_2 }
            { BASE }
            { limb_add_carry() }
            { expected_sum}
            OP_EQUALVERIFY
            { expected_carry }
            OP_EQUALVERIFY
            { BASE }
            OP_EQUALVERIFY
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the `limb_sub_carry` method for subtracting two limbs.
///
/// It generates random 30-bit limbs and initializes a base of 2^30 and
/// then verifies the correctness of the output.
#[test]
fn test_limb_sub_carry() {
    const BASE: i32 = 1 << 30;
    const TESTS_NUMBER: usize = 50;

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        // Generate two limbs
        let limb_1: i32 = prng.gen_range(0..1 << 30);
        let limb_2: i32 = prng.gen_range(0..1 << 30);

        let expected_carry = (limb_1 - limb_2 < 0) as i32;
        let expected_sub = limb_1 - limb_2 + expected_carry * BASE;

        let script = script! {
            { limb_1 }
            { limb_2 }
            { BASE }
            { limb_sub_carry() }
            { expected_sub}
            OP_EQUALVERIFY
            { expected_carry }
            OP_EQUALVERIFY
            { BASE }
            OP_EQUALVERIFY
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_64_and_254_bit_increment() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (a.clone().add(BigUint::one())).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_ADD1() }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: u64 = prng.gen();
        let c = a.wrapping_add(1u64);

        let script = script! {
            { U64::OP_PUSH_U64LESLICE(&[a]) }
            { U64::OP_ADD1() }
            { U64::OP_PUSH_U64LESLICE(&[c]) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the multiplication of two 254-bit numbers and two 64-bit numbers.
#[test]
fn test_64_and_254_bit_mul() {
    print_script_size("254-bit mul", U254::OP_MUL());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..3 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = a.clone().mul(b.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_MUL() }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..3 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        let b: BigUint = prng.sample(RandomBits::new(64));
        let c: BigUint = (a.clone().mul(b.clone())).rem(BigUint::one().shl(64));

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U64::OP_MUL() }
            { U64::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U64::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the multiplication of two 254-bit numbers and two 64-bit numbers.
#[test]
fn test_254_bit_widening_mul() {
    const TESTS_NUMBER: usize = 10;

    print_script_size(
        "254-bit widening mul",
        U254::handle_OP_WIDENINGMUL::<U508>(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = a.clone() * b.clone();

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_WIDENINGMUL::<U508>() }
            { U508::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U508::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the multiplication of two 254-bit numbers using w width approach.
#[test]
fn test_mul_w_width_254bit() {
    const TESTS_NUM: usize = 10;
    const WIDTH: usize = 4;

    type U254Windowed = NonNativeWindowedBigIntImpl<U254, WIDTH>;

    print_script_size("254-bit w-width mul", U254Windowed::OP_MUL());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = a.clone().mul(b.clone()).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254Windowed::OP_MUL() }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

// Tests the multiplication of two 254-bit numbers and two 64-bit numbers.
#[test]
fn test_254_bit_windowed_widening_mul() {
    const TESTS_NUMBER: usize = 10;

    print_script_size(
        "254-bit widening mul",
        U254Windowed::handle_OP_WIDENINGMUL::<U508>(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUMBER {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = a.clone() * b.clone();

        let script = script! {
            { U254Windowed::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254Windowed::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254Windowed::OP_WIDENINGMUL::<U508>() }
            { U508::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U508::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
