use num_bigint::BigUint;
use num_traits::Num;
use std::str::FromStr;

use crate::bigint::U254;
use crate::pseudo::{OP_4BITMUL, OP_4MUL, OP_CLONE};
use crate::traits::integer::NonNativeInteger;
use crate::treepp::*;

use super::NonNativeBigInt;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigInt<N_BITS, LIMB_SIZE> {
    /// Pushes 0 to the stack
    pub(super) fn handle_OP_0() -> Script {
        OP_CLONE(0, Self::N_LIMBS)
    }

    /// Pushes 1 to the stack
    pub(super) fn handle_OP_1() -> Script {
        script! {
            1
            { OP_CLONE(0, Self::N_LIMBS - 1) }
        }
    }

    /// Pushes the given decimal string to the stack.
    pub fn handle_OP_PUSHDECSTR(dec_string: &str) -> Script {
        Self::OP_PUSHU32LESLICE(&BigUint::from_str(dec_string).unwrap().to_u32_digits())
    }

    /// Pushes the given hexadecimal string to the stack.
    pub fn handle_OP_PUSHHEX(hex_string: &str) -> Script {
        Self::OP_PUSHU32LESLICE(
            &BigUint::from_str_radix(hex_string, 16)
                .unwrap()
                .to_u32_digits(),
        )
    }

    /// Zip two elements at specified depths.
    ///
    /// **Input:** `a0,...,a{N-1},b0,...,b{N-1}`
    ///
    /// **Output:** `a0,b0,...,a{N-1},b{N-1}`
    pub(super) fn handle_OP_ZIP(depth_1: usize, depth_2: usize) -> Script {
        let depth_1 = (depth_1 + 1) * Self::N_LIMBS - 1;
        let depth_2 = (depth_2 + 1) * Self::N_LIMBS - 1;

        assert_ne!(depth_1, depth_2, "cannot zip the same element");

        if depth_1 < depth_2 {
            return script! {
                for i in 0..Self::N_LIMBS {
                    { depth_1 + i }
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
                { depth_2 + i + 1 }
                OP_ROLL
            }
        }
    }

    pub(super) fn handle_OP_DUPZIP(depth: usize) -> Script {
        let depth = (depth + 1) * Self::N_LIMBS - 1;

        script! {
            for i in 0..Self::N_LIMBS {
                { depth + i } OP_ROLL OP_DUP
            }
        }
    }

    /// Pushes the given [`u32`]` array given in little-endian format to the stack
    /// in low-endian format (meaning, the top element in the stack contains
    /// the lowest limb).
    pub(super) fn handle_OP_PUSHU32LESLICE(v: &[u32]) -> Script {
        let mut limbs = Self::transform_le_limbs(v);
        limbs.reverse();

        script! {
            for limb in &limbs {
                { *limb }
            }
        }
    }

    /// Pushes the given [`u64`] array given in little-endian format to the stack
    /// in big-endian format.
    pub(super) fn handle_OP_PUSHU64LESLICE(v: &[u64]) -> Script {
        // Converting the u64 array to u32 array and doing
        // the same operation as in push_u32_le
        let v = v
            .iter()
            .flat_map(|v| {
                [
                    (v & 0xffffffffu64) as u32,
                    ((v >> 32) & 0xffffffffu64) as u32,
                ]
            })
            .collect::<Vec<u32>>();

        Self::handle_OP_PUSHU32LESLICE(&v)
    }

    /// Copies the [`BigInt`] located at depth `depth` to the top of the stack.
    /// Works similarly to `OP_PICK`, but for big integers.
    ///
    /// For example, calling `copy(0)` will copy the top element to the top of the stack, while
    /// calling `copy(1)` will copy the second element to the top of the stack.
    pub(super) fn handle_OP_PICK(depth: usize) -> Script {
        let depth = (depth + 1) * Self::N_LIMBS;

        script! {
            { depth }
            for _ in 0..Self::N_LIMBS - 1 {
                OP_DUP OP_PICK OP_SWAP
            }
            OP_1SUB OP_PICK
        }
    }

    /// Copies the big integer located at depth to the top of the stack.
    /// Works similarly to `OP_PICK`, but for big integers.
    ///
    /// For example, calling `copy(0)` will copy the top element to the top of the stack, while
    /// calling `copy(1)` will copy the second element to the top of the stack.
    pub(super) fn handle_OP_PICKSTACK() -> Script {
        script! {
            { Self::normalize_stack_depth() }

            for _ in 0..Self::N_LIMBS - 1 {
                OP_DUP OP_PICK OP_SWAP
            }
            OP_1SUB OP_PICK
        }
    }

    /// Pulls the big integer located at depth `depth` to the top of the stack and
    /// removes the original element.
    pub(super) fn handle_OP_ROLL(depth: usize) -> Script {
        let depth = (depth + 1) * Self::N_LIMBS - 1;

        script! {
            for _ in 0..Self::N_LIMBS {
                { depth } OP_ROLL
            }
        }
    }

    /// Swaps top two `BigInt`s from the stack.
    pub(super) fn handle_OP_SWAP() -> Script {
        Self::OP_ROLL(1)
    }

    /// Removes the top [`BigInt`] from the stack.
    pub(super) fn handle_OP_DROP() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS / 2 {
                OP_2DROP
            }
            if Self::N_LIMBS & 1 == 1 {
                OP_DROP
            }
        }
    }

    /// Pushes the given [`BigInt`] to the altstack.
    pub(super) fn handle_OP_TOALTSTACK() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_TOALTSTACK
            }
        }
    }

    /// Pushes the given [`BigInt`] from the altstack to the main stack.
    pub(super) fn handle_OP_FROMALTSTACK() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_FROMALTSTACK
            }
        }
    }

    /// Copies two [`BigInt`]s at corresponding depths and zips them together.
    pub(super) fn handle_OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script {
        let depth_1 = (depth_1 + 1) * Self::N_LIMBS - 1;
        let depth_2 = (depth_2 + 1) * Self::N_LIMBS - 1;

        script! {
            for i in 0..Self::N_LIMBS {
                { depth_1 + i } OP_PICK
                { depth_2 + 1 + i } OP_PICK
            }
        }
    }
}

impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigInt<N_BITS, LIMB_SIZE> {
    /// Since internal representation of limbs is not the power of two, we transform the
    /// power-two representation to the limb representation (e.g., for 254-bit integer, we
    /// have 9 limbs of 30 bits each). Returns an array of limbs in low-endian format.
    pub(super) fn transform_le_limbs(v: &[u32]) -> Vec<u32> {
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
            let mut element = 0u32;
            for (i, chunk_element) in chunk_vec.iter().enumerate().take(LIMB_SIZE) {
                if *chunk_element {
                    element += 1 << i;
                }
            }

            limbs.push(element);
        }

        // Asserting that we have not exceeded the number of limbs
        assert!(limbs.len() <= Self::N_LIMBS, "limbs number is too-large");

        // Filling the rest of the limbs with zeros to ensure the constant size
        limbs.resize(Self::N_LIMBS, 0);
        assert_eq!(limbs.len(), Self::N_LIMBS, "limbs length is incorrect");

        limbs
    }

    /// Since copy operation requires input depth to be equal to
    /// `Self::N_LIMBS * (depth+1)`, this function normalizes the depth
    /// to the required value.
    fn normalize_stack_depth() -> Script {
        if Self::N_LIMBS == U254::N_LIMBS {
            return script! {
                1 OP_ADD // Adding 1 to the depth
                OP_DUP OP_4MUL {crate::pseudo::OP_2MUL()} // Multiplying 1+depth by 8
                OP_ADD // Adding 1+depth to 8*(1+depth) to get 9*(1+depth)
            };
        }

        script! {
            1 OP_ADD
            { Self::N_LIMBS }
            OP_4BITMUL // Multiplying 1+depth by the number of limbs
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
}

#[cfg(test)]
mod test {
    use crate::bigint::{NonNativeBigInt, U254};
    use crate::traits::integer::NonNativeInteger;
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
                { NonNativeBigInt::<N_BITS, 30>::OP_ZIP(1, 0) }
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
                { NonNativeBigInt::<N_BITS, 30>::OP_ZIP(0, 1) }
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
                { U254::OP_PICK(1) }

                // Assert that the copied number is equal to the original
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }

                // Dropping both numbers since they are not needed
                { U254::OP_DROP() }
                { U254::OP_DROP() }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    /// Tests the copy operation when performed with the depth of 1
    /// using the variable from the stack
    #[test]
    fn test_copy_depth_1_from_stack() {
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
                { 1 }
                { U254::OP_PICKSTACK() }

                // Assert that the copied number is equal to the original
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }

                // Dropping both numbers since they are not needed
                { U254::OP_DROP() }
                { U254::OP_DROP() }
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
                { U254::OP_PICK(0) }

                // Assert that the copied number is equal to the original
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }

                // Dropping both numbers since they are not needed
                { U254::OP_DROP() }
                { U254::OP_DROP() }
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
                { U254::OP_ROLL(1) }
                for i in 0..N_U30_LIMBS {
                    { expected[(N_U30_LIMBS - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::OP_DROP() }
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
                { U254::OP_PICKZIP(1, 0) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::OP_DROP() }
                { U254::OP_DROP() }
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
                { U254::OP_PICKZIP(0, 1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::OP_DROP() }
                { U254::OP_DROP() }
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
                { U254::OP_PICKZIP(1, 1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::OP_DROP() }
                { U254::OP_DROP() }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);

            let script = script! {
                for i in 0..N_U30_LIMBS * 2 {
                    { v[i as usize] }
                }
                { U254::OP_DUPZIP(1) }
                for i in 0..N_U30_LIMBS * 2 {
                    { expected[(N_U30_LIMBS * 2 - 1 - i) as usize] }
                    OP_EQUALVERIFY
                }
                { U254::OP_DROP() }
                OP_TRUE
            };
            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn push_hex() {
        let exec_result = execute_script(script! {
            { U254::OP_PUSHHEXSTR("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47") }
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
