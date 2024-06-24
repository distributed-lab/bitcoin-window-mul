use num_bigint::BigUint;
use num_traits::Num;
use std::str::FromStr;

use crate::bigint::BigInt;
use crate::pseudo::push_to_stack;
use crate::treepp::*;

impl<const N_BITS: usize, const LIMB_SIZE: usize> BigInt<N_BITS, LIMB_SIZE> {
    /// Since internal representation of limbs is not the power of two, we transform the
    /// power-two representation to the limb representation (e.g., for 254-bit integer, we
    /// have 9 limbs of 30 bits each). Returns an array of limbs in low-endian format.
    pub fn transform_le_limbs(v: &[u32]) -> Vec<u32> {
        // Forming an array of N_BITS bits from the input (v)
        let mut bits = vec![];
        for elem in v.iter() {
            for i in 0..32 {
                bits.push((elem & (1 << i)) != 0);
            }
        }

        // Filling the rest of the bits with zeros
        bits.resize(N_BITS, false);
        assert_eq!(bits.len(), N_BITS, "bits length is incorrect");

        // Forming limbs from the bits, combined in chunks of size LIMB_SIZE
        let mut limbs = vec![];
        for chunk in bits.chunks(LIMB_SIZE) {
            let mut chunk_vec = chunk.to_vec();
            // For the last chunk, we need to fill it with zeros
            chunk_vec.resize(LIMB_SIZE, false);

            // Converting the chunk to a limb of size LIMB_SIZE
            let mut elem = 0u32;
            for i in 0..LIMB_SIZE {
                if chunk_vec[i] {
                    elem += 1 << i;
                }
            }

            limbs.push(elem);
        }

        // Asserting that we have not exceeded the number of limbs
        assert!(limbs.len() <= Self::N_LIMBS, "limbs number is too-large");

        // Filling the rest of the limbs with zeros to ensure the constant size
        limbs.resize(Self::N_LIMBS, 0);
        assert_eq!(limbs.len(), Self::N_LIMBS, "limbs length is incorrect");

        limbs
    }

    /// Pushes the given u32 array given in little-endian format to the stack
    /// in low-endian format (meaning, the top element in the stack contains
    /// the lowest limb).
    pub fn push_u32_le(v: &[u32]) -> Script {
        let mut limbs = Self::transform_le_limbs(v);
        limbs.reverse();

        script! {
            for limb in &limbs {
                { *limb }
            }
        }
    }

    /// Pushes the given u64 array given in little-endian format to the stack
    /// in big-endian format.
    pub fn push_u64_le(v: &[u64]) -> Script {
        let v = v
            .iter()
            .flat_map(|v| {
                [
                    (v & 0xffffffffu64) as u32,
                    ((v >> 32) & 0xffffffffu64) as u32,
                ]
            })
            .collect::<Vec<u32>>();

        Self::push_u32_le(&v)
    }

    /// Zip two elements at specified depths.
    ///
    /// **Input:** `a0,...,a{N-1},b0,...,b{N-1}`
    ///
    /// **Output:** `a0,b0,...,a{N-1},b{N-1}`
    pub fn zip(depth_1: u32, depth_2: u32) -> Script {
        let depth_1 = (depth_1 + 1) * (Self::N_LIMBS as u32) - 1;
        let depth_2 = (depth_2 + 1) * (Self::N_LIMBS as u32) - 1;

        assert_ne!(depth_1, depth_2, "cannot zip the same element");

        if depth_1 < depth_2 {
            return script! {
                for i in 0..Self::N_LIMBS {
                    { depth_1 + (i as u32) }
                    OP_ROLL
                    { depth_2 }
                    OP_ROLL
                }
            };
        }

        script! {
            for i in 0..Self::N_LIMBS {
                { depth_1 }
                OP_ROLL
                { depth_2 + (i as u32) + 1 }
                OP_ROLL
            }
        }
    }

    pub fn copy_zip(mut a: u32, mut b: u32) -> Script {
        a = (a + 1) * (Self::N_LIMBS as u32) - 1;
        b = (b + 1) * (Self::N_LIMBS as u32) - 1;

        script! {
            for i in 0..Self::N_LIMBS {
                { a + (i as u32) } OP_PICK { b + 1 + (i as u32) } OP_PICK
            }
        }
    }

    pub fn dup_zip(mut a: u32) -> Script {
        a = (a + 1) * (Self::N_LIMBS as u32) - 1;

        script! {
            for i in 0..Self::N_LIMBS {
                { a + (i as u32) } OP_ROLL OP_DUP
            }
        }
    }

    /// Copies the big integer located at depth `depth` to the top of the stack.
    /// Works similarly to `OP_PICK`, but for big integers.
    ///
    /// For example, calling `copy(0)` will copy the top element to the top of the stack, while
    /// calling `copy(1)` will copy the second element to the top of the stack.
    pub fn copy(depth: u32) -> Script {
        let depth = (depth + 1) * (Self::N_LIMBS as u32);

        script! {
            { depth }
            for _ in 0..Self::N_LIMBS - 1 {
                OP_DUP OP_PICK OP_SWAP
            }
            OP_1SUB OP_PICK
        }
    }

    /// Pulls the big integer located at depth `depth` to the top of the stack and
    /// removes the original element.
    pub fn roll(depth: u32) -> Script {
        let depth = (depth + 1) * (Self::N_LIMBS as u32) - 1;

        script! {
            for _ in 0..Self::N_LIMBS {
                { depth } OP_ROLL
            }
        }
    }

    pub fn drop() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS / 2 {
                OP_2DROP
            }
            if Self::N_LIMBS & 1 == 1 {
                OP_DROP
            }
        }
    }

    pub fn push_dec(dec_string: &str) -> Script {
        Self::push_u32_le(&BigUint::from_str(dec_string).unwrap().to_u32_digits())
    }

    pub fn push_hex(hex_string: &str) -> Script {
        Self::push_u32_le(
            &BigUint::from_str_radix(hex_string, 16)
                .unwrap()
                .to_u32_digits(),
        )
    }

    #[inline]
    pub fn push_zero() -> Script {
        push_to_stack(0, Self::N_LIMBS as usize)
    }

    #[inline]
    pub fn push_one() -> Script {
        script! {
            { push_to_stack(0,(Self::N_LIMBS - 1) as usize) }
            1
        }
    }

    pub fn is_zero_keep_element(a: u32) -> Script {
        let a = (Self::N_LIMBS as u32) * a;
        script! {
            1
            for i in 0..Self::N_LIMBS {
                { a + (i as u32) + 1 } OP_PICK
                OP_NOT
                OP_BOOLAND
            }
        }
    }

    pub fn is_zero(a: u32) -> Script {
        let a = (Self::N_LIMBS as u32) * a;
        script! {
            1
            for _ in 0..Self::N_LIMBS {
                { a +1 } OP_ROLL
                OP_NOT
                OP_BOOLAND
            }
        }
    }

    pub fn is_one_keep_element(a: u32) -> Script {
        let a = (Self::N_LIMBS as u32) * a;
        script! {
            1
            { a + 1 } OP_PICK
            1 OP_EQUAL OP_BOOLAND
            for i in 1..Self::N_LIMBS {
                { a + (i as u32) + 1 } OP_PICK
                OP_NOT
                OP_BOOLAND
            }
        }
    }

    pub fn is_one(a: u32) -> Script {
        let a = (Self::N_LIMBS as u32) * a;
        script! {
            1
            { a + 1 } OP_ROLL
            1 OP_EQUAL OP_BOOLAND
            for _ in 1..Self::N_LIMBS {
                { a + 1 } OP_ROLL
                OP_NOT
                OP_BOOLAND
            }
        }
    }

    pub fn toaltstack() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_TOALTSTACK
            }
        }
    }

    pub fn fromaltstack() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_FROMALTSTACK
            }
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::{BigInt, U254};
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
                { BigInt::<N_BITS, 30>::zip(1, 0) }
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
                { BigInt::<N_BITS, 30>::zip(0, 1) }
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
                { U254::copy(1) }

                // Assert that the copied number is equal to the original
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }

                // Dropping both numbers since they are not needed
                { U254::drop() }
                { U254::drop() }
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
                { U254::copy(0) }

                // Assert that the copied number is equal to the original
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }

                // Dropping both numbers since they are not needed
                { U254::drop() }
                { U254::drop() }
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
                { U254::roll(1) }
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::drop() }
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
                { U254::copy_zip(1, 0) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::drop() }
                { U254::drop() }
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
                { U254::copy_zip(0, 1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::drop() }
                { U254::drop() }
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
                { U254::copy_zip(1, 1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::drop() }
                { U254::drop() }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);

            let script = script! {
                for i in 0..N_U30_LIMBS * 2 {
                    { v[i as usize] }
                }
                { U254::dup_zip(1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::drop() }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn push_hex() {
        let exec_result = execute_script(script! {
            { U254::push_hex("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47") }
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
}
