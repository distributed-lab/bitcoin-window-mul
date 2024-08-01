use num_bigint::BigUint;
use num_traits::Num;
use std::str::FromStr;

use crate::bigint::{NonNativeBigIntImpl, U254, U508};
use crate::pseudo::{OP_4BITMUL, OP_4MUL, OP_CLONE};
use crate::traits::integer::{NonNativeInteger, NonNativeLimbInteger};
use crate::treepp::*;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    /// Pushes 0 to the stack
    pub(in super::super) fn handle_OP_0() -> Script {
        OP_CLONE(0, Self::N_LIMBS)
    }

    /// Pushes 1 to the stack
    pub(in super::super) fn handle_OP_1() -> Script {
        script! {
            1
            { OP_CLONE(0, Self::N_LIMBS - 1) }
        }
    }

    /// Pushes the given decimal string to the stack.
    pub(in super::super) fn handle_OP_PUSHDECSTR(dec_string: &str) -> Script {
        Self::OP_PUSH_U32LESLICE(&BigUint::from_str(dec_string).unwrap().to_u32_digits())
    }

    /// Pushes the given hexadecimal string to the stack.
    pub(in super::super) fn handle_OP_PUSHHEX(hex_string: &str) -> Script {
        Self::OP_PUSH_U32LESLICE(
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
    pub(in super::super) fn handle_OP_ZIP(depth_1: usize, depth_2: usize) -> Script {
        // If the depths are equal, we just perform the dupzip
        if depth_1 == depth_2 {
            return Self::handle_OP_DUPZIP(depth_1);
        }

        // Normalizing the depths
        let depth_1 = (depth_1 + 1) * Self::N_LIMBS - 1;
        let depth_2 = (depth_2 + 1) * Self::N_LIMBS - 1;

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

    pub(in super::super) fn handle_OP_DUPZIP(depth: usize) -> Script {
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
    pub(in super::super) fn handle_OP_PUSHU32LESLICE(v: &[u32]) -> Script {
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
    pub(in super::super) fn handle_OP_PUSHU64LESLICE(v: &[u64]) -> Script {
        // Converting the u64 array to u32 array and doing
        // the same operation as in push_u32_le
        let v = v
            .iter()
            .flat_map(|v| {
                [
                    (v & (u32::MAX as u64)) as u32,
                    ((v >> 32) & (u32::MAX as u64)) as u32,
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
    pub(in super::super) fn handle_OP_PICK(depth: usize) -> Script {
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
    pub(in super::super) fn handle_OP_PICKSTACK() -> Script {
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
    pub(in super::super) fn handle_OP_ROLL(depth: usize) -> Script {
        let depth = (depth + 1) * Self::N_LIMBS - 1;

        script! {
            for _ in 0..Self::N_LIMBS {
                { depth } OP_ROLL
            }
        }
    }

    /// Swaps top two `BigInt`s from the stack.
    pub(in super::super) fn handle_OP_SWAP() -> Script {
        Self::OP_ROLL(1)
    }

    /// Removes the top [`BigInt`] from the stack.
    pub(in super::super) fn handle_OP_DROP() -> Script {
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
    pub(in super::super) fn handle_OP_TOALTSTACK() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_TOALTSTACK
            }
        }
    }

    /// Pushes the given [`BigInt`] from the altstack to the main stack.
    pub(in super::super) fn handle_OP_FROMALTSTACK() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS {
                OP_FROMALTSTACK
            }
        }
    }

    /// Copies two [`BigInt`]s at corresponding depths and zips them together.
    pub(in super::super) fn handle_OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script {
        let depth_1 = (depth_1 + 1) * Self::N_LIMBS - 1;
        let depth_2 = (depth_2 + 1) * Self::N_LIMBS - 1;

        script! {
            for i in 0..Self::N_LIMBS {
                { depth_1 + i } OP_PICK
                { depth_2 + 1 + i } OP_PICK
            }
        }
    }

    /// Extends the big integer to the specified type.
    pub(in super::super) fn handle_OP_EXTEND<T>() -> Script
    where
        T: NonNativeLimbInteger,
    {
        assert!(
            T::N_BITS > Self::N_BITS,
            "The integer to be extended must have more bits than the current integer"
        );
        assert!(
            T::LIMB_SIZE == Self::LIMB_SIZE,
            "The integers to be extended must have the same number of bits in limb"
        );

        let n_limbs_self = (Self::N_BITS + Self::LIMB_SIZE - 1) / Self::LIMB_SIZE;
        let n_limbs_extension = (T::N_BITS + T::LIMB_SIZE - 1) / T::LIMB_SIZE;
        let n_limbs_add = n_limbs_extension - n_limbs_self;

        if n_limbs_add == 0 {
            return script! {};
        }

        script! {
            { OP_CLONE(0, n_limbs_add) } // Pushing zeros to the stack
            for _ in 0..n_limbs_self {
                { n_limbs_extension - 1 } OP_ROLL
            }
        }
    }
}

impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
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
        match Self::N_LIMBS {
            U254::N_LIMBS => script! {
                1 OP_ADD // Adding 1 to the depth
                // Then, we need to multiply by 9
                OP_DUP OP_4MUL {crate::pseudo::OP_2MUL()} // Multiplying 1+depth by 8
                OP_ADD // Adding 1+depth to 8*(1+depth) to get 9*(1+depth)
            },
            U508::N_LIMBS => script! {
                1 OP_ADD // Adding 1 to the depth
                // Then, we need to multiply by 17:
                OP_DUP OP_4MUL OP_4MUL // Multiplying 1+depth by 8
                OP_ADD // Adding 1+depth to 8*(1+depth) to get 9*(1+depth)
            },
            _ => script! {
                1 OP_ADD
                { Self::N_LIMBS }
                OP_4BITMUL // Multiplying 1+depth by the number of limbs
            },
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
