use crate::bigint::NonNativeBigIntImpl;
use crate::pseudo::{OP_3DROP, OP_BITAND};
use crate::traits::bitable::Bitable;
use crate::treepp::*;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    /// Takes the top stack big integer and outputs
    /// the naf representation in the main stack
    pub fn convert_to_be_naf_bits() -> Script {
        script! {
            { <Self as Bitable>::OP_TOBEBITS_TOALTSTACK() }
            { binary_to_be_naf(N_BITS) }
        }
    }

    /// Takes the top stack big integer and outputs
    /// the naf representation in the alt stack
    pub fn convert_to_be_naf_bits_toaltstack() -> Script {
        script! {
            { Self::OP_TOBEBITS_TOALTSTACK() }
            { binary_to_be_naf(N_BITS) }

            // Moving everything to the alt stack
            // NOTE: The naf representation is one bit longer than the binary one
            for _ in 0..N_BITS + 1 {
                OP_TOALTSTACK
            }
        }
    }
}

/// Given bit and carry, conducts the following:
///
/// 1. If carry is `0`, does noting.
/// 2. If carry is `1`, if the bit is `0`, sets the bit to `1` and carry to `0`.
/// 3. If carry is `1`, if the bit is `1`, sets the bit to `0` and does not modify carry.
fn bit_add_carry() -> Script {
    // TODO: This can be probably optimized
    script! {
        OP_DUP
        OP_IF
            // Checking the last bit
            OP_SWAP
            OP_DUP
            OP_IF
                // In case the last bit is 1, we set it to 0 and do not change carry
                OP_DROP 0 OP_SWAP
            OP_ELSE
                // In case the last bit is 0, we set it to 1 and change carry to 0
                OP_DROP 1
                OP_SWAP
                OP_DROP 0
            OP_ENDIF
        OP_ENDIF
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// NAF representation with a size `num_bits+1`.
/// It pushes all the bits to the alt stack except for the most significant bit.
/// The first element in the alt stack (except for one left in the main stack)
/// is the least significant limb.
pub fn binary_to_be_naf(num_bits: usize) -> Script {
    script! {
        // We also have top two stack elements + carry in the front
        OP_FROMALTSTACK
        0 // Carry initialization

        for _ in 0..num_bits - 1 {
            OP_FROMALTSTACK
            OP_SWAP
            // At this point, we have two bits and carry at the front

            bit_add_carry // Add the last bit and carry

            // Now we have the last bit in the stack and carry in the front
            // Checking whether we get the pattern {1,1} and in case we do, we need to change it to {-1,0},
            // and change the carry accordingly (to 1)

            // From (bit1, bit2, carry) to (carry, bit1, bit2)
            OP_ROT OP_ROT

            // Checking whether bit1 = bit2 = 1
            OP_2DUP OP_BITAND OP_IF
                // In case they are both 1, we need to change them to -1 and 0, while the carry must be one
                OP_3DROP
                1 (-1) 0
            OP_ENDIF

            OP_ROT
        }
    }
}
