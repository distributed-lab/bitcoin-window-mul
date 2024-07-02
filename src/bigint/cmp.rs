use crate::treepp::*;

use super::NonNativeBigInt;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigInt<N_BITS, LIMB_SIZE> {
    /// Checks whether the number at specified depth
    /// is zero and removes it from the stack
    pub(super) fn handle_OP_ISZERO(depth: usize) -> Script {
        let depth = Self::N_LIMBS * depth;
        script! {
            1
            for _ in 0..Self::N_LIMBS {
                { depth+1 } OP_ROLL
                OP_NOT
                OP_BOOLAND
            }
        }
    }

    /// Verifies that two [`BigInt`]s on the stack are equal at the specified
    /// depths. For example, `OP_EQUALVERIFY(1, 0)` will verify that the top two big integers
    /// are equal. If two depths are equal, the script will be empty.
    pub fn handle_OP_EQUALVERIFY(depth_1: usize, depth_2: usize) -> Script {
        if depth_1 == depth_2 {
            return script! {};
        }
        script! {
            { Self::handle_OP_ZIP(depth_1, depth_2) }
            for _ in 0..Self::N_LIMBS {
                OP_EQUALVERIFY
            }
        }
    }

    /// Checks whether two [`BigInt`]s are equal at specified depths.
    /// For example, `eq(1, 0)` will check whether the top two big integers are equal.
    pub(super) fn handle_OP_EQUAL(depth_1: usize, depth_2: usize) -> Script {
        if depth_1 == depth_2 {
            return script! { OP_EQUAL };
        }

        // General idea: compare each limb from the end to the beginning, push
        // the result to the alt stack, and then AND all the results from the alt stack.
        script! {
            { Self::handle_OP_ZIP(depth_1, depth_2) }
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

    /// Checks whether two [`BigInt`]s are not equal.
    pub fn handle_OP_NOTEQUAL(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_EQUAL(depth_1, depth_2) }
            OP_NOT
        }
    }

    /// Returns whether `a < b`
    pub fn handle_OP_LESSTHAN(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_ZIP(depth_1, depth_2) }
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
    pub fn handle_OP_LESSOREQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_GREATEROREQUAL(depth_2, depth_1)
    }

    /// Returns whether `a > b`
    pub fn handle_OP_GREATERTHAN(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_LESSOREQUAL(depth_1, depth_2) }
            OP_NOT
        }
    }

    // Returns whether `a >= b`
    pub fn handle_OP_GREATEROREQUAL(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_LESSTHAN(depth_1, depth_2) }
            OP_NOT
        }
    }
}
#[cfg(test)]
mod test {
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U64::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U64::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U64::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U64::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
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
                { U64::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U64::OP_ISZERO(0) }
                OP_NOT
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }

        let script = script! {
            { U254::OP_PUSHU32LESLICE(&[0]) }
            { U254::is_zero_keep_element(0) }
            OP_TOALTSTACK
            { U254::OP_DROP() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U254::OP_PUSHU32LESLICE(&[0]) }
            { U254::OP_ISZERO(0) }
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U64::OP_PUSHU32LESLICE(&[0]) }
            { U64::is_zero_keep_element(0) }
            OP_TOALTSTACK
            { U64::OP_DROP() }
            OP_FROMALTSTACK
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            { U64::OP_PUSHU32LESLICE(&[0]) }
            { U64::OP_ISZERO(0) }
        };
        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
