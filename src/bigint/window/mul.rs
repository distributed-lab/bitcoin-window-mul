use crate::bigint::window::precompute::WindowedPrecomputeTable;
use crate::traits::integer::NonNativeLimbInteger;
use crate::traits::window::Windowable;
use crate::treepp::*;

use super::NonNativeWindowedBigIntImpl;

#[allow(non_snake_case)]
impl<T, const WIDTH: usize> NonNativeWindowedBigIntImpl<T, WIDTH>
where
    T: NonNativeLimbInteger,
{
    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition.
    pub(in super::super) fn handle_OP_MUL() -> Script {
        script! {
            // Convert to w-width form.
            { <Self as Windowable>::OP_TOBEWINDOWEDFORM_TOALTSTACK() }

            // Precomputing {0*z, 1*z, ..., ((1<<WIDTH)-1)*z}
            { WindowedPrecomputeTable::<T, WIDTH>::initialize() }

            // We initialize the result
            { T::OP_0() }

            for _ in 0..Self::DECOMPOSITION_SIZE {
                // Double the result WIDTH times
                for _ in 0..WIDTH {
                    { T::OP_2MUL(0) }
                }

                // Picking di from the stack
                OP_FROMALTSTACK

                // Add the precomputed value to the result.
                // Since currently stack looks like:
                // {0*z, 1*z, ..., ((1<<WIDTH)-1)*z, r, di} with
                // r being the result, we need to copy
                // (1<<WIDTH - di)th element to the top of the stack.
                { 1<<WIDTH }
                OP_SWAP
                OP_SUB
                { T::OP_PICKSTACK() }
                { T::OP_ADD(0, 1) }
            }

            // Clearing the precomputed values from the stack.
            { T::OP_TOALTSTACK() }
            for _ in 0..1<<WIDTH {
                { T::OP_DROP() }
            }
            { T::OP_FROMALTSTACK() }
        }
    }
}
