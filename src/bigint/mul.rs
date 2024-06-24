use crate::bigint::BigInt;
use crate::treepp::{pushable, script, Script};

impl<const N_BITS: usize, const LIMB_SIZE: usize> BigInt<N_BITS, LIMB_SIZE> {
    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs using
    /// binary decomposition.
    pub fn mul() -> Script {
        script! {
            // We save the binary representation of the first number in the stack
            // to the alt stack.
            { Self::convert_to_be_bits_toaltstack() }

            // Pushing zero to the stack.
            { Self::zero() }

            // Further strategy is approximately as follows:
            // Initialized zero is the result while the first number is the temporary variable.
            // On each step, double the temporary value and add result to the temporary variable if
            // the current bit is 1. Continue through all bits.

            OP_FROMALTSTACK
            OP_IF
                { Self::copy(1) }
                { Self::add(1, 0) }
            OP_ENDIF

            for _ in 1..N_BITS - 1 {
                { Self::roll(1) }
                { Self::double(0) }
                { Self::roll(1) }
                OP_FROMALTSTACK
                OP_IF
                    { Self::copy(1) }
                    { Self::add(1, 0) }
                OP_ENDIF
            }

            { Self::roll(1) }
            { Self::double(0) }
            OP_FROMALTSTACK
            OP_IF
                { Self::add(1, 0) }
            OP_ELSE
                { Self::drop() }
            OP_ENDIF
        }
    }

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using naf decomposition.
    pub fn mul_naf() -> Script {
        // TODO: Make it work
        script! {
            // We save the naf representation of the first number in the stack
            // to the alt stack.
            { Self::convert_to_be_naf_bits_toaltstack() }

            // Pushing zero to the stack.
            { Self::zero() }

            // Further strategy is approximately as follows:
            // Initialized zero is the result while the first number is the temporary variable.
            // On each step, double the temporary value and add result to the temporary variable if
            // the current bit is 1. Continue through all bits.

            OP_FROMALTSTACK
            OP_DUP 0 OP_EQUAL OP_NEGATE
            OP_IF
                1 OP_EQUAL OP_IF
                    { Self::copy(1) }
                    { Self::add(1, 0) }
                OP_ELSE
                    { Self::copy(1) }
                    { Self::sub(1, 0) }
                OP_ENDIF
            OP_ENDIF

            for _ in 1..N_BITS - 1 {
                { Self::roll(1) }
                { Self::double(0) }
                { Self::roll(1) }
                OP_FROMALTSTACK
                OP_DUP 0 OP_EQUAL OP_NEGATE
                OP_IF
                    1 OP_EQUAL OP_IF
                        { Self::copy(1) }
                        { Self::add(1, 0) }
                    OP_ELSE
                        { Self::copy(1) }
                        { Self::sub(1, 0) }
                    OP_ENDIF
                OP_ENDIF
            }

            { Self::roll(1) }
            { Self::double(0) }
            OP_FROMALTSTACK
            OP_DUP 0 OP_EQUAL OP_NEGATE
            OP_IF
                1 OP_EQUAL OP_IF
                    { Self::add(1, 0) }
                OP_ELSE
                    { Self::sub(1, 0) }
                OP_ENDIF
            OP_ELSE
                { Self::drop() }
            OP_ENDIF
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::{U254, U64};
    use crate::{print_script_size, treepp::*};
    use core::ops::{Mul, Rem, Shl};
    use num_bigint::{BigUint, RandomBits};
    use num_traits::One;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    /// Tests the multiplication of two 254-bit numbers and two 64-bit numbers.
    #[test]
    fn test_mul() {
        print_script_size("254-bit mul", U254::mul());

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..3 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let b: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = a.clone().mul(b.clone()).rem(BigUint::one().shl(254));

            let mul_script = U254::mul();

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { mul_script }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::eq_verify(1, 0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            println!("Result: {:?}", exec_result);

            assert!(exec_result.success);
        }

        for _ in 0..3 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            let b: BigUint = prng.sample(RandomBits::new(64));
            let c: BigUint = (a.clone().mul(b.clone())).rem(BigUint::one().shl(64));

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::mul() }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::eq_verify(1, 0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    /// Tests the multiplication of two 254-bit numbers using wnaf approach.
    #[test]
    fn test_mul_wnaf() {
        const TESTS_NUM: usize = 10;
        print_script_size("254-bit mul", U254::mul_naf());

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let b: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = a.clone().mul(b.clone()).rem(BigUint::one().shl(254));

            let mul_script = U254::mul_naf();

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { mul_script }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::eq_verify(1, 0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            println!("Result: {:?}", exec_result);

            assert!(exec_result.success);
        }
    }
}
