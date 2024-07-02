use crate::{bigint::NonNativeBigIntImpl, treepp::*};
use std::cmp::min;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    pub(in super::super) fn handle_OP_TOBEBITS() -> Script {
        script! {
            for i in 0..Self::N_LIMBS - 1 {
                { limb_to_be_bits(LIMB_SIZE) }
                { LIMB_SIZE * (i + 1) } OP_ROLL
            }
            { limb_to_be_bits(N_BITS - LIMB_SIZE * (Self::N_LIMBS - 1)) }
        }
    }

    pub(in super::super) fn handle_OP_TOLEBITS() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS - 1 {
                OP_TOALTSTACK
            }
            { limb_to_le_bits(N_BITS - LIMB_SIZE * (Self::N_LIMBS - 1)) }
            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
                { limb_to_le_bits(LIMB_SIZE) }
            }
        }
    }

    pub(in super::super) fn handle_OP_TOBEBITS_TOALTSTACK() -> Script {
        script! {
            { Self::N_LIMBS - 1 } OP_ROLL
            { limb_to_be_bits_toaltstack(Self::HEAD) }
            for i in 0..Self::N_LIMBS - 1 {
                { Self::N_LIMBS - 2 - i } OP_ROLL
                { limb_to_be_bits_toaltstack(LIMB_SIZE) }
            }
        }
    }

    pub(in super::super) fn handle_OP_TOLEBITS_TOALTSTACK() -> Script {
        script! {
            for _ in 0..Self::N_LIMBS - 1 {
                { limb_to_le_bits_toaltstack(LIMB_SIZE) }
            }
            { limb_to_le_bits_toaltstack(N_BITS - LIMB_SIZE * (Self::N_LIMBS - 1)) }
        }
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// big-endian bits. It pushes all the bits to the alt stack
/// except for the most significant bit. The first element in the alt stack
/// (except for one left in the main stack) is the least significant bit.
pub fn limb_to_be_bits_common(num_bits: usize) -> Script {
    /// We will push `{2, 2^2, 2^3, ..., 2^{num_bits - 1}}` to the stack.
    /// For some reasons, pushing first numbers manually and others by doubling
    /// is more efficient than pushing all numbers by doubling.
    /// Thus, this constant is a number of powers of two to push manually if
    /// `num_bits` is large enough.
    const MANUAL_POWERS_OF_TWO_PUSHES: usize = 14;

    // If the number of bits is less than `MANUAL_POWERS_OF_TWO_PUSHES`, we will
    // push all powers of 2 manually.
    let power_of_two_pushes = min(MANUAL_POWERS_OF_TWO_PUSHES, num_bits - 1);

    script! {
        // Pop the element to the altstack, we will return it in a moment
        OP_TOALTSTACK

        // Push the powers of 2 onto the stack
        // First, all powers of 2 that we can push as 3-byte numbers
        for i in 0..power_of_two_pushes  {
            { 2 << i }
        }
        // Then, we double powers of 2 to generate the 4-byte numbers
        for _ in power_of_two_pushes..num_bits - 1 {
            OP_DUP
            OP_DUP
            OP_ADD
        }

        // Bringing the original limb back to the stack
        OP_FROMALTSTACK

        // We will now compare the limb with the powers of 2. If
        // the number is less that this power, we will add 0 to the alt stack
        // and pop this power. Otherwise, we will subtract this power from the
        // limb and push 1 to the alt stack.
        for _ in 0..num_bits - 2 {
            OP_2DUP OP_LESSTHANOREQUAL
            OP_IF
                OP_SWAP OP_SUB 1
            OP_ELSE
                OP_NIP 0
            OP_ENDIF
            OP_TOALTSTACK
        }

        // Do not forget about the last power of 2 (1) since we have not
        // processed it in the loop above
        OP_2DUP OP_LESSTHANOREQUAL
        OP_IF
            OP_SWAP OP_SUB 1
        OP_ELSE
            OP_NIP 0
        OP_ENDIF
    }
}

fn limb_to_le_bits_common(num_bits: usize) -> Script {
    let min_i = min(22, num_bits - 1);
    script! {
        // Push the powers of 2 onto the stack
        // First, all powers of 2 that we can push as 3-byte numbers
        for i in 0..min_i - 1  {
            { 2 << i } OP_TOALTSTACK
        }
        if num_bits - 1 > min_i {
            { 2 << (min_i - 1) } OP_DUP OP_TOALTSTACK

            // Then, we double powers of 2 to generate the 4-byte numbers
            for _ in min_i..num_bits - 2 {
                OP_DUP
                OP_ADD
                OP_DUP OP_TOALTSTACK
            }

            OP_DUP
            OP_ADD OP_TOALTSTACK
        } else {
            { 2 << (min_i - 1) } OP_TOALTSTACK
        }

        for _ in 0..num_bits - 2 {
            OP_FROMALTSTACK
            OP_2DUP OP_GREATERTHANOREQUAL
            OP_IF
                OP_SUB 1
            OP_ELSE
                OP_DROP 0
            OP_ENDIF
            OP_SWAP
        }

        OP_FROMALTSTACK
        OP_2DUP OP_GREATERTHANOREQUAL
        OP_IF
            OP_SUB 1
        OP_ELSE
            OP_DROP 0
        OP_ENDIF

        OP_SWAP
    }
}

pub fn limb_to_le_bits(num_bits: usize) -> Script {
    if num_bits >= 2 {
        script! {
            { limb_to_le_bits_common(num_bits) }
        }
    } else {
        script! {}
    }
}

pub fn limb_to_le_bits_toaltstack(num_bits: usize) -> Script {
    if num_bits >= 2 {
        script! {
            { limb_to_le_bits_common(num_bits) }
            for _ in 0..num_bits {
                OP_TOALTSTACK
            }
        }
    } else {
        script! {}
    }
}

pub fn limb_to_be_bits(num_bits: usize) -> Script {
    if num_bits < 2 {
        return script! {};
    }

    script! {
        { limb_to_be_bits_common(num_bits) }
        for _ in 0..num_bits - 2 {
            OP_FROMALTSTACK
        }
    }
}

pub fn limb_to_be_bits_toaltstack(num_bits: usize) -> Script {
    if num_bits >= 2 {
        script! {
            { limb_to_be_bits_common(num_bits) }
            OP_TOALTSTACK
            OP_TOALTSTACK
        }
    } else {
        script! {
            OP_TOALTSTACK
        }
    }
}
