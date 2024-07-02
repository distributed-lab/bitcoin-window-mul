use crate::bigint::{Comparable, U254, U64};
use crate::traits::integer::NonNativeInteger;
use crate::treepp::*;
use core::cmp::Ordering;
use num_bigint::{BigUint, RandomBits};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_u254_cmp() {
    let mut prng = ChaCha20Rng::seed_from_u64(2);

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let a_lessthan = if a.cmp(&b) == Ordering::Less {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_LESSTHAN(1, 0) }
            { a_lessthan }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let a_lessthanorequal = if a.cmp(&b) != Ordering::Greater {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_LESSOREQUAL(1, 0) }
            { a_lessthanorequal }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let a_greaterthan = if a.cmp(&b) == Ordering::Greater {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_GREATERTHAN(1, 0) }
            { a_greaterthan }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let a_greaterthanorequal = if a.cmp(&b) != Ordering::Less {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U254::OP_GREATEROREQUAL(1, 0) }
            { a_greaterthanorequal }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_u64_cmp() {
    let mut prng = ChaCha20Rng::seed_from_u64(2);

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        let b: BigUint = prng.sample(RandomBits::new(64));
        let a_lessthan = if a.cmp(&b) == Ordering::Less {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U64::OP_LESSTHAN(1, 0) }
            { a_lessthan }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        let b: BigUint = prng.sample(RandomBits::new(64));
        let a_lessthanorequal = if a.cmp(&b) != Ordering::Greater {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U64::OP_LESSOREQUAL(1, 0) }
            { a_lessthanorequal }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        let b: BigUint = prng.sample(RandomBits::new(64));
        let a_greaterthan = if a.cmp(&b) == Ordering::Greater {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U64::OP_GREATERTHAN(1, 0) }
            { a_greaterthan }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        let b: BigUint = prng.sample(RandomBits::new(64));
        let a_greaterthanorequal = if a.cmp(&b) != Ordering::Less {
            1u32
        } else {
            0u32
        };

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_PUSH_U32LESLICE(&b.to_u32_digits()) }
            { U64::OP_GREATEROREQUAL(1, 0) }
            { a_greaterthanorequal }
            OP_EQUAL
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_is_zero() {
    let mut prng = ChaCha20Rng::seed_from_u64(2);

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        // assume that it would never be a zero when sampling a random element

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::is_zero_keep_element(0) }
            OP_NOT OP_TOALTSTACK
            { U254::OP_DROP() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(254));
        // assume that it would never be a zero when sampling a random element

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_ISZERO(0) }
            OP_NOT
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        // assume that it would never be a zero when sampling a random element

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::is_zero_keep_element(0) }
            OP_NOT OP_TOALTSTACK
            { U64::OP_DROP() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let a: BigUint = prng.sample(RandomBits::new(64));
        // assume that it would never be a zero when sampling a random element

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_ISZERO(0) }
            OP_NOT
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    let script = script! {
        { U254::OP_PUSH_U32LESLICE(&[0]) }
        { U254::is_zero_keep_element(0) }
        OP_TOALTSTACK
        { U254::OP_DROP() }
        OP_FROMALTSTACK
    };
    let exec_result = execute_script(script);
    assert!(exec_result.success);

    let script = script! {
        { U254::OP_PUSH_U32LESLICE(&[0]) }
        { U254::OP_ISZERO(0) }
    };
    let exec_result = execute_script(script);
    assert!(exec_result.success);

    let script = script! {
        { U64::OP_PUSH_U32LESLICE(&[0]) }
        { U64::is_zero_keep_element(0) }
        OP_TOALTSTACK
        { U64::OP_DROP() }
        OP_FROMALTSTACK
    };
    let exec_result = execute_script(script);
    assert!(exec_result.success);

    let script = script! {
        { U64::OP_PUSH_U32LESLICE(&[0]) }
        { U64::OP_ISZERO(0) }
    };
    let exec_result = execute_script(script);
    assert!(exec_result.success);
}
