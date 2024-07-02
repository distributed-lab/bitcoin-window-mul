use crate::bigint::NonNativeBigInt;
use crate::treepp::*;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigInt<N_BITS, LIMB_SIZE> {
    /// Adds two [`BigInt`]s from the stack, resulting in a new [`BigInt`] at the top of the stack.
    pub(super) fn handle_OP_ADD(depth_1: usize, depth_2: usize) -> Script {
        script! {
            // Zip the two BigInts from the stack
            { Self::handle_OP_ZIP(depth_1, depth_2) }

            // Push the base to the stack
            { Self::BASE }

            // Add two limbs, take the sum to the alt stack
            limb_add_carry OP_TOALTSTACK

            for _ in 0..Self::N_LIMBS - 2 {
                // Since we have {an} {bn} {base} {carry} in the stack, where an, bn
                // represent the limbs, we do the following:
                // OP_ROT: {a1} {base} {carry} {a2}
                // OP_ADD: {a1} {base} {carry+a2}
                // OP_SWAP: {a1} {carry+a2} {base}
                // Then we add (a1+a2+carry) and repeat
                OP_ROT
                OP_ADD
                OP_SWAP
                limb_add_carry OP_TOALTSTACK
            }

            // When we got (a1, b1, base, carry) on the stack, we drop the base, add carry to b1,
            // and conduct the addition without returning a carry.
            OP_NIP
            OP_ADD
            { limb_add_nocarry(Self::HEAD_OFFSET) }

            // Take all limbs from the sum to the main stack
            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }

    /// Doubles the [`BigInt`] at specified `depth`, resulting
    /// in a new [`BigInt`] at the top of the stack.
    pub(super) fn handle_OP2MUL(depth: usize) -> Script {
        script! {
            { Self::handle_OP_DUPZIP(depth) }

            { Self::BASE }

            // A0 + B0
            limb_add_carry OP_TOALTSTACK

            // from     A1      + B1        + carry_0
            //   to     A{N-2}  + B{N-2}    + carry_{N-3}
            for _ in 0..Self::N_LIMBS - 2 {
                OP_ROT
                OP_ADD
                OP_SWAP
                limb_add_carry OP_TOALTSTACK
            }

            // A{N-1} + B{N-1} + carry_{N-2}
            OP_NIP
            OP_ADD
            { limb_add_nocarry(Self::HEAD_OFFSET) }

            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }

    /// Subtracts the top [`BigInt`] from the second top [`BigInt`] on the stack.
    pub(super) fn handle_OPSUB(depth_1: usize, depth_2: usize) -> Script {
        script! {
            // Zip the two BigInts from the stack
            { Self::handle_OP_ZIP(depth_1, depth_2) }

            // Push the base to the stack
            { Self::BASE }

            // Subtract two limbs, take the sum to the alt stack
            limb_sub_carry OP_TOALTSTACK

            for _ in 0..Self::N_LIMBS - 2 {
                // Here, we have {an} {bn} {base} {carry} in the stack
                OP_ROT
                OP_ADD
                OP_SWAP
                limb_sub_carry OP_TOALTSTACK
            }

            // When we got (a1, b1, base, carry) on the stack, we drop the base, add carry to b1,
            // and conduct the subtraction without carry.
            OP_NIP
            OP_ADD
            { limb_sub_nocarry(Self::HEAD_OFFSET) }

            // Take all limbs from the sum to the main stack
            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }

    /// Adds one to the top [`BigInt`] on the stack.
    pub(super) fn handle_OPADD1() -> Script {
        script! {
            1
            { 1 << LIMB_SIZE }

            // A0 + 1
            limb_add_carry OP_TOALTSTACK

            // from     A1        + carry_0
            //   to     A{N-2}    + carry_{N-3}
            for _ in 0..Self::N_LIMBS - 2 {
                OP_SWAP
                limb_add_carry OP_TOALTSTACK
            }

            // A{N-1} + carry_{N-2}
            OP_NIP
            { limb_add_nocarry(Self::HEAD_OFFSET) }

            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }
}

/// Compute the sum of two limbs, including the carry bit.
///
/// **Input**: `{num1} {num2} {base}`
///
/// **Output**: `{base} {carry} {sum}`
///
/// where `sum` is `num1+num2` if `carry` is `0`, and `num1+num2-base` if `carry` is `1`.
///
/// Optimized by: @stillsaiko
pub fn limb_add_carry() -> Script {
    script! {
        OP_ROT OP_ROT
        OP_ADD OP_2DUP
        OP_LESSTHANOREQUAL
        OP_TUCK
        OP_IF
            2 OP_PICK OP_SUB
        OP_ENDIF
    }
}

/// Compute the difference between two limbs, including the carry bit.
///
/// **Input**: `{num1} {num2} {base}`
///
/// **Output**: `{base} {carry} {sub}`
///
/// where `sub` is `num1-num2` if `carry` is `0`, and `base+(num1-num2)` if `carry` is `1`.
pub fn limb_sub_carry() -> Script {
    script! {
        OP_ROT OP_ROT
        OP_SUB
        OP_DUP
        0
        OP_LESSTHAN
        OP_TUCK
        OP_IF
            2 OP_PICK OP_ADD
        OP_ENDIF
    }
}

/// Compute the sum of two limbs, dropping the carry bit
///
/// Optimized by: @wz14
pub fn limb_add_nocarry(head_offset: u32) -> Script {
    script! {
        OP_ADD { head_offset } OP_2DUP
        OP_GREATERTHANOREQUAL
        OP_IF
            OP_SUB
        OP_ELSE
            OP_DROP
        OP_ENDIF
    }
}

/// Compute the sub of two limbs, dropping the carry bit
pub fn limb_sub_nocarry(head_offset: u32) -> Script {
    script! {
        OP_SUB 0 OP_2DUP
        OP_LESSTHAN
        OP_IF
            {head_offset} OP_ADD
        OP_ELSE
            OP_DROP
        OP_ENDIF
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::add::{limb_add_carry, limb_sub_carry};
    use crate::bigint::{Comparable, U254, U64};
    use crate::traits::arithmeticable::Arithmeticable;
    use crate::traits::integer::NonNativeInteger;
    use crate::{print_script_size, treepp::*};
    use core::ops::{Add, Rem, Shl};
    use num_bigint::{BigUint, RandomBits, ToBigUint};
    use num_traits::One;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_add() {
        print_script_size("254_bit_add", U254::OP_ADD(1, 0));

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let b: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = (a.clone() + b.clone()).rem(BigUint::one().shl(254));

            let script = script! {
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
                { U254::OP_ADD(1, 0) }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
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
                { U64::OP_PUSHU64LESLICE(&[a]) }
                { U64::OP_PUSHU64LESLICE(&[b]) }
                { U64::OP_ADD(1, 0) }
                { U64::OP_PUSHU64LESLICE(&[c]) }
                { U64::OP_EQUALVERIFY(1, 0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_sub() {
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_PUSHU32LESLICE(&b.to_u32_digits()) }
                { U254::OP_SUB(1, 0) }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
                { U254::OP_EQUALVERIFY(1, 0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_double() {
        print_script_size("u254_double", U254::OP_2MUL(0));

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = (a.clone() + a.clone()).rem(BigUint::one().shl(254));

            let script = script! {
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_2MUL(0) }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
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
                { U64::OP_PUSHU64LESLICE(&[a]) }
                { U64::OP_2MUL(0) }
                { U64::OP_PUSHU64LESLICE(&[c]) }
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
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_2MUL(0) }
                { U254::OP_2MUL(0) }
                { U254::OP_2MUL(0) }
                { U254::OP_2MUL(0) }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
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
                { U64::OP_PUSHU64LESLICE(&[a]) }
                { U64::OP_2MUL(0) }
                { U64::OP_PUSHU64LESLICE(&[c]) }
                { U64::OP_EQUALVERIFY(1, 0) }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_256_mul() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = (256.to_biguint().unwrap() * a.clone()).rem(BigUint::one().shl(254));

            let script = script! {
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                for _ in 0..8 {
                    { U254::OP_2MUL(0) }
                }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
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
                { U64::OP_PUSHU64LESLICE(&[a]) }
                { U64::OP_2MUL(0) }
                { U64::OP_PUSHU64LESLICE(&[c]) }
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
    fn test_increment() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = (a.clone().add(BigUint::one())).rem(BigUint::one().shl(254));

            let script = script! {
                { U254::OP_PUSHU32LESLICE(&a.to_u32_digits()) }
                { U254::OP_ADD1() }
                { U254::OP_PUSHU32LESLICE(&c.to_u32_digits()) }
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
                { U64::OP_PUSHU64LESLICE(&[a]) }
                { U64::OP_ADD1() }
                { U64::OP_PUSHU64LESLICE(&[c]) }
                { U64::OP_EQUALVERIFY(1, 0) }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }
}
