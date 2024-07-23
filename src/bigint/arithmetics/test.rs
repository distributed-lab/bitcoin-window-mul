use crate::bigint::arithmetics::add::{
    limb_add_carry, limb_doubling_initial_carry, limb_sub_carry,
};
use crate::bigint::implementation::NonNativeBigIntImpl;
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
use std::env::{var, VarError};
use std::str::FromStr;
use std::sync::LazyLock;

static LAZY_TESTS: LazyLock<bool> = LazyLock::new(|| {
    match var("LAZY_TESTS") {
        Ok(var) => match var.as_str(){
            "true" => true,
            "false" => false,
            _ => panic!("Can not determine the value of LAZY_TESTS environment variable - if must be `true` or `false`"),
        },
        Err(VarError::NotPresent) => true,
        Err(VarError::NotUnicode(_)) => panic!("Can not determine the value of LAZY_TESTS environment variable: not unicode"),

}
});

static TESTS_NUMBER: LazyLock<usize> = LazyLock::new(|| if *LAZY_TESTS { 10 } else { 1000 });

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
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 100 } else { 1000 };

    print_script_size("508_bit_add", U508::OP_ADD(1, 0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
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
fn test_508_bit_add_no_overflow() {
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 100 } else { 1000 };

    print_script_size("508_bit_add_no_overflow", U508::OP_ADD_NOOVERFLOW(1, 0));

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let a: BigUint = prng.sample(RandomBits::new(507));
        let b: BigUint = prng.sample(RandomBits::new(507));
        let c: BigUint = a.clone() + b.clone();

        let script = script! {
            { U508::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U508::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U508::OP_ADD_NOOVERFLOW(1, 0) }
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
fn test_254_bit_double_no_overflow() {
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 100 } else { 1000 };

    print_script_size(
        "u254_double_no_overflow",
        U254::handle_OP_2MUL_NOOVERFLOW(0),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        let a: BigUint = prng.sample(RandomBits::new(253));
        let c: BigUint = a.clone() + a.clone();

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::handle_OP_2MUL_NOOVERFLOW(0) }
            { U254::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U254::OP_EQUALVERIFY(1, 0) }
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
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 50 } else { 500 };

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
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

/// Tests the `limb_double_carry` method for doubling the limb.
///
/// It generates a random 30-bit limb and initializes a base of 2^30 and
/// then verifies the correctness of the output.
#[test]
fn test_limb_doubling_initial_carry() {
    const BASE: u32 = 1 << 30;
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 50 } else { 500 };

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
        // Generate two limbs
        let limb: u32 = prng.gen_range(0..1 << 30);

        let expected_carry = (2 * limb >= BASE) as u32;
        let expected_double = 2 * limb - expected_carry * BASE;

        let script = script! {
            { limb }
            { BASE }
            { limb_doubling_initial_carry() }
            { expected_double }
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
    #[allow(non_snake_case)]
    let TESTS_NUM: usize = if *LAZY_TESTS { 50 } else { 500 };

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..TESTS_NUM {
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
fn test_64_and_254_bit_narrow_mul() {
    print_script_size("254-bit narrow naive mul", U254::OP_MUL());

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

/// Tests the widening multiplication of two 254-bit numbers using initial BitVM approach.
#[test]
fn test_254_bit_naive_widening_mul() {
    print_script_size(
        "254-bit widening naive mul",
        U254::handle_OP_WIDENINGMUL::<U508>(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
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

/// Tests the multiplication of two 254-bit numbers using w-width approach.
#[test]
fn test_254_bit_narrow_mul_w_width() {
    const WIDTH: usize = 4;

    type U254Windowed = NonNativeWindowedBigIntImpl<U254, WIDTH>;

    print_script_size("254-bit w-width narrow mul", U254Windowed::OP_MUL());

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
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

// Tests the widening multiplication of two 254-bit integers to get a 508-bit one.
#[test]
fn test_254_bit_windowed_lazy_widening_mul() {
    print_script_size(
        "254-bit w-width lazy widening mul",
        U254Windowed::handle_lazy_OP_WIDENINGMUL::<U508>(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
        let a: BigUint = prng.sample(RandomBits::new(100));
        let b: BigUint = prng.sample(RandomBits::new(100));
        let c: BigUint = a.clone() * b.clone();

        let script = script! {
            { U254Windowed::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254Windowed::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254Windowed::handle_lazy_OP_WIDENINGMUL::<U508>() }
            { U508::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U508::OP_EQUALVERIFY(1, 0) }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests OP_PICKSTACK version when the top stack element is
/// larger than the ones that is being picked before it.
#[test]
fn test_op_pick_stack_and_add_different_bits() {
    type U456 = NonNativeBigIntImpl<456, 30>;

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
        // Generating 4 254-bit numbers and put 456-bit number in the front
        let a1: BigUint = prng.sample(RandomBits::new(254));
        let a2: BigUint = prng.sample(RandomBits::new(254));
        let a3: BigUint = prng.sample(RandomBits::new(254));
        let a4: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(456));

        // Here, we:
        // 1. Push a1, a2, a3, a4, b
        // 2. Pick 4th element from the top (that is, a2)
        // 3. Extending a2 to 456 bits
        // 4. Pushing a2 again and verify that we indeed got a2 from picking
        // 5. Dropping all remaining elements
        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a1.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&a2.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&a3.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&a4.to_u32_digits()) }
            { U456::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { 3 }
            { U254Windowed::handle_OP_PICKSTACK::<U456>() }
            { U254::OP_EXTEND::<U456>() }
            { U456::OP_PUSH_U32LESLICE(&a2.to_u32_digits()) }
            { U456::OP_EQUALVERIFY(1, 0) }
            { U456::OP_DROP() }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            { U254::OP_DROP() }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the intermediate step of the optimized multiplication which
/// multiplies by (1<<WIDTH) and adds precomputed 256-bit value to the
/// result.
#[test]
fn test_optimized_multiplication_step() {
    type U268 = NonNativeBigIntImpl<268, 30>;
    // UInt that is by 4 bits larger than the regular one.
    // This is done due to the fact that we need to multiply
    // by 16 on each step and therefore we need to allocate
    // additional space before conducting operations
    type U272 = NonNativeBigIntImpl<272, 30>;

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
        // On each step we want to get 16*a + b, where a is initially
        // 268 bits and later extended to 272 bits, and b is 256 bits.
        let a: BigUint = prng.sample(RandomBits::new(268));
        let b: BigUint = prng.sample(RandomBits::new(256));
        let c: BigUint = a
            .clone()
            .mul(BigUint::from_str("16").unwrap())
            .add(b.clone());

        let script = script! {
            { U268::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }

            { U268::OP_EXTEND::<U272>() }
            for _ in 0..4 {
                { U272::OP_2MUL_NOOVERFLOW(0) }
            }

            { U268::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_EXTEND::<U272>() }
            { U272::OP_ADD_NOOVERFLOW(0, 1) }
            { U272::OP_PUSH_U32LESLICE(&c.to_u32_digits()) }
            { U272::OP_EQUALVERIFY(0, 1) }

            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

/// Tests the multiplication of two 254-bit numbers using a
/// super optimized method.
#[test]
fn test_254_bit_windowed_widening_optimized_mul() {
    print_script_size(
        "254-bit optimized widening mul",
        U254Windowed::OP_WIDENINGMUL::<U508>(),
    );

    let mut prng = ChaCha20Rng::seed_from_u64(0);
    for _ in 0..*TESTS_NUMBER {
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
