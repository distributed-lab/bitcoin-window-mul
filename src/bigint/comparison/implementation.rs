use crate::{bigint::NonNativeBigIntImpl, treepp::*};

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    /// Checks whether the number at specified depth
    /// is zero and removes it from the stack
    pub(in super::super) fn handle_OP_ISZERO(depth: usize) -> Script {
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
    pub(in super::super) fn handle_OP_EQUALVERIFY(depth_1: usize, depth_2: usize) -> Script {
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
    pub(in super::super) fn handle_OP_EQUAL(depth_1: usize, depth_2: usize) -> Script {
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
    pub(in super::super) fn handle_OP_NOTEQUAL(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_EQUAL(depth_1, depth_2) }
            OP_NOT
        }
    }

    /// Returns whether `a < b`
    pub(in super::super) fn handle_OP_LESSTHAN(depth_1: usize, depth_2: usize) -> Script {
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
    pub(in super::super) fn handle_OP_LESSOREQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_GREATEROREQUAL(depth_2, depth_1)
    }

    /// Returns whether `a > b`
    pub(in super::super) fn handle_OP_GREATERTHAN(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_LESSOREQUAL(depth_1, depth_2) }
            OP_NOT
        }
    }

    // Returns whether `a >= b`
    pub(in super::super) fn handle_OP_GREATEROREQUAL(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { Self::handle_OP_LESSTHAN(depth_1, depth_2) }
            OP_NOT
        }
    }
}
