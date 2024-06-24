use crate::bigint::BigInt;
use crate::treepp::*;

impl<const N_BITS: usize, const LIMB_SIZE: usize> BigInt<N_BITS, LIMB_SIZE> {
    /// Verifies that the top two big integers on the stack are equal at the specified
    /// depths. For example, `eq_verify(1, 0)` will verify that the top two big integers
    /// are equal. If two depths are equal, the script will be empty.
    pub fn eq_verify(depth_1: u32, depth_2: u32) -> Script {
        if depth_1 == depth_2 {
            return script! {};
        }
        script! {
            { Self::zip(depth_1, depth_2) }
            for _ in 0..Self::N_LIMBS {
                OP_EQUALVERIFY
            }
        }
    }

    /// Checks whether two `BigInt`s are equal at specified depths.
    /// For example, `eq(1, 0)` will check whether the top two big integers are equal.
    pub fn eq(depth_1: u32, depth_2: u32) -> Script {
        if depth_1 == depth_2 {
            return script! { OP_EQUAL };
        }

        // General idea: compare each limb from the end to the beginning, push
        // the result to the alt stack, and then AND all the results from the alt stack.
        script! {
            { Self::zip(depth_1, depth_2) }
            for _ in 0..Self::N_LIMBS {
                OP_EQUAL
                OP_TOALTSTACK
            }
            for _ in 0..Self::N_LIMBS {
                OP_FROMALTSTACK
            }
            for _ in 0..Self::N_LIMBS - 1 {
                OP_BOOLAND
            }
        }
    }

    /// Checks whether two `BigInt`s are not equal.
    pub fn neq(a: u32, b: u32) -> Script {
        script! {
            { Self::eq(a, b) }
            OP_NOT
        }
    }

    /// Returns whether `a < b`
    pub fn lt(a: u32, b: u32) -> Script {
        script! {
            { Self::zip(a, b) }
            OP_2DUP
            OP_GREATERTHAN OP_TOALTSTACK
            OP_LESSTHAN OP_TOALTSTACK

            for _ in 0..Self::N_LIMBS - 1 {
                OP_2DUP
                OP_GREATERTHAN OP_TOALTSTACK
                OP_LESSTHAN OP_TOALTSTACK
            }

            OP_FROMALTSTACK OP_FROMALTSTACK
            OP_OVER OP_BOOLOR

            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
                OP_FROMALTSTACK
                OP_ROT
                OP_IF
                    OP_2DROP 1
                OP_ELSE
                    OP_ROT OP_DROP
                    OP_OVER
                    OP_BOOLOR
                OP_ENDIF
            }

            OP_BOOLAND
        }
    }

    /// Returns whether `a <= b`
    pub fn leq(a: u32, b: u32) -> Script {
        Self::geq(b, a)
    }

    /// Returns whether `a > b`
    pub fn gt(a: u32, b: u32) -> Script {
        script! {
            { Self::leq(a, b) }
            OP_NOT
        }
    }

    // Returns whether `a >= b`
    pub fn geq(a: u32, b: u32) -> Script {
        script! {
            { Self::lt(a, b) }
            OP_NOT
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::{U254, U64};
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
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::lt(1, 0) }
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
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::leq(1, 0) }
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
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::gt(1, 0) }
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
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::geq(1, 0) }
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
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::lt(1, 0) }
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
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::leq(1, 0) }
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
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::gt(1, 0) }
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
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::geq(1, 0) }
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
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::is_zero_keep_element(0) }
                OP_NOT OP_TOALTSTACK
                { U254::drop() }
                OP_FROMALTSTACK
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            // assume that it would never be a zero when sampling a random element

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::is_zero(0) }
                OP_NOT
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            // assume that it would never be a zero when sampling a random element

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::is_zero_keep_element(0) }
                OP_NOT OP_TOALTSTACK
                { U64::drop() }
                OP_FROMALTSTACK
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            // assume that it would never be a zero when sampling a random element

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::is_zero(0) }
                OP_NOT
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }

        let script = script! {
            { U254::push_u32_le(&[0]) }
            { U254::is_zero_keep_element(0) }
            OP_TOALTSTACK
            { U254::drop() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U254::push_u32_le(&[0]) }
            { U254::is_zero(0) }
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U64::push_u32_le(&[0]) }
            { U64::is_zero_keep_element(0) }
            OP_TOALTSTACK
            { U64::drop() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U64::push_u32_le(&[0]) }
            { U64::is_zero(0) }
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
