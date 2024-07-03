use crate::bigint::window::precompute::WindowedPrecomputeTable;
use crate::bigint::window::NonNativeWindowedBigIntImpl;
use crate::traits::integer::NonNativeLimbInteger;
use crate::traits::window::Windowable;
use crate::{
    bigint::NonNativeBigIntImpl,
    treepp::{pushable, script, Script},
};

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    pub(in super::super) fn handle_OP_MUL() -> Script {
        script! {
            { Self::handle_OP_TOBEBITS_TOALTSTACK() }

            { Self::handle_OP_0() }

            OP_FROMALTSTACK
            OP_IF
                { Self::handle_OP_PICK(1) }
                { Self::handle_OP_ADD(1, 0) }
            OP_ENDIF

            for _ in 1..N_BITS - 1 {
                { Self::handle_OP_ROLL(1) }
                { Self::handle_OP_2MUL(0) }
                { Self::handle_OP_ROLL(1) }
                OP_FROMALTSTACK
                OP_IF
                    { Self::handle_OP_PICK(1) }
                    { Self::handle_OP_ADD(1, 0) }
                OP_ENDIF
            }

            { Self::handle_OP_ROLL(1) }
            { Self::handle_OP_2MUL(0) }
            OP_FROMALTSTACK
            OP_IF
                { Self::handle_OP_ADD(1, 0) }
            OP_ELSE
                { Self::handle_OP_DROP() }
            OP_ENDIF

        }
    }

    pub(in super::super) fn handle_OP_WIDENINGMUL<T>() -> Script
    where
        T: NonNativeLimbInteger,
    {
        script! {
            { Self::handle_OP_TOBEBITS_TOALTSTACK() }

            { Self::handle_OP_EXTEND::<T>() }

            { T::OP_0() }

            OP_FROMALTSTACK
            OP_IF
                { T::OP_PICK(1) }
                { T::OP_ADD(1, 0) }
            OP_ENDIF

            for _ in 1..Self::N_BITS - 1 {
                { T::OP_ROLL(1) }
                { T::OP_2MUL(0) }
                { T::OP_ROLL(1) }
                OP_FROMALTSTACK
                OP_IF
                    { T::OP_PICK(1) }
                    { T::OP_ADD(1, 0) }
                OP_ENDIF
            }

            { T::OP_ROLL(1) }
            { T::OP_2MUL(0) }
            OP_FROMALTSTACK
            OP_IF
                { T::OP_ADD(1, 0) }
            OP_ELSE
                { T::OP_DROP() }
            OP_ENDIF

        }
    }
}

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

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition to get twice as large integer.
    pub(in super::super) fn handle_OP_WIDENINGMUL<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        script! {
            // Convert to w-width form.
            { <Self as Windowable>::OP_TOBEWINDOWEDFORM_TOALTSTACK() }

            // Extend to larger integer
            { T::OP_EXTEND::<Q>() }

            // Precomputing {0*z, 1*z, ..., ((1<<WIDTH)-1)*z}
            { WindowedPrecomputeTable::<Q, WIDTH>::initialize() }

            // We initialize the result
            { Q::OP_0() }

            for _ in 0..Self::DECOMPOSITION_SIZE {
                // Double the result WIDTH times
                for _ in 0..WIDTH {
                    { Q::OP_2MUL(0) }
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
                { Q::OP_PICKSTACK() }
                { Q::OP_ADD(0, 1) }
            }

            // Clearing the precomputed values from the stack.
            { Q::OP_TOALTSTACK() }
            for _ in 0..1<<WIDTH {
                { Q::OP_DROP() }
            }
            { Q::OP_FROMALTSTACK() }
        }
    }
}
