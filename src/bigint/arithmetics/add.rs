use crate::bigint::NonNativeBigIntImpl;
use crate::treepp::*;

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    /// Adds two [`BigInt`]s from the stack, resulting in a new [`BigInt`] at the top of the stack.
    pub(in super::super) fn handle_OP_ADD(depth_1: usize, depth_2: usize) -> Script {
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
    pub(in super::super) fn handle_OP_2MUL(depth: usize) -> Script {
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
    pub(in super::super) fn handle_OP_SUB(depth_1: usize, depth_2: usize) -> Script {
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
    pub(in super::super) fn handle_OP_ADD1() -> Script {
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
