use bitcoin::opcodes::all::{OP_ADD, OP_FROMALTSTACK, OP_SUB, OP_SWAP};
use bitcoin_script_stack::debugger::pushable::Builder;
use seq_macro::seq;

use crate::bigint::window::precompute::WindowedPrecomputeTable;
use crate::bigint::window::NonNativeWindowedBigIntImpl;
use crate::bigint::{U254Windowed, U508};
use crate::pseudo::OP_4MUL;
use crate::traits::arithmeticable::Arithmeticable;
use crate::traits::integer::{NonNativeInteger, NonNativeLimbInteger};
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
            { WindowedPrecomputeTable::<T, WIDTH, false>::initialize() }

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
            { WindowedPrecomputeTable::<Q, WIDTH, true>::initialize() }

            // Picking di from the stack
            OP_FROMALTSTACK 1 OP_ADD

            // Add the precomputed value to the result.
            // Since currently stack looks like:
            // {0*z, 1*z, ..., ((1<<WIDTH)-1)*z, di} with
            // r being the result, we need to copy
            // (1<<WIDTH - di)th element to the top of the stack.
            { 1<<WIDTH }
            OP_SWAP
            OP_SUB
            { Q::OP_PICKSTACK() }

            for _ in 1..Self::DECOMPOSITION_SIZE {
                // Double the result WIDTH times
                for _ in 0..WIDTH {
                    { Q::OP_2MUL_NOOVERFLOW(0) }
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
                { Q::OP_ADD_NOOVERFLOW(0, 1) }
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

#[allow(non_snake_case)]
impl U254Windowed {
    /// Since copy operation requires input depth to be equal to
    /// `Self::SELF_LIMBS + Self::OTHER_LIMBS * depth`, this function normalizes the depth
    /// to the required value.
    fn normalize_stack_depth<Q: NonNativeLimbInteger>() -> Script {
        let q_n_limbs = (Q::N_BITS + Q::LIMB_SIZE - 1) / Q::LIMB_SIZE;
        script! {
            OP_DUP OP_4MUL {crate::pseudo::OP_2MUL()} // Multiplying depth by 8
            OP_ADD // Adding depth to 8*depth to get 9*depth
            { q_n_limbs }
            OP_ADD
        }
    }

    /// Copies the big integer located at depth to the top of the stack.
    /// Works similarly to `OP_PICK`, but for big integers.
    ///
    /// For example, calling `copy(0)` will copy the top element to the top of the stack, while
    /// calling `copy(1)` will copy the second element to the top of the stack.
    pub(in super::super) fn handle_OP_PICKSTACK<Q: NonNativeLimbInteger>() -> Script {
        let n_limbs = (Self::N_BITS + Self::LIMB_SIZE - 1) / Self::LIMB_SIZE;

        script! {
            { Self::normalize_stack_depth::<Q>() }

            for _ in 0..n_limbs - 1 {
                OP_DUP OP_PICK OP_SWAP
            }
            OP_1SUB OP_PICK
        }
    }

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition to get twice as large integer.
    pub(in super::super) fn handle_optimized_OP_WIDENINGMUL() -> Script {
        pushable::Builder::new()
            // Push w-width form to the stack
            .push_expression(Self::OP_TOBEWINDOWEDFORM_TOALTSTACK())
            // Initialize precompute table to the stack
            // Since 256 bits fits in 9x30 limbs, we do not need
            // to extend anything
            .push_expression(WindowedPrecomputeTable::<Self, 4, true>::initialize())
            // Making the first iteration of the loop (without the initial doubling step) 
            // Taking coefficient, finding 16-coefficient and picking 
            // corresponding precomputed value
            .push_opcode(OP_FROMALTSTACK)
            .push_expression(1)
            .push_opcode(OP_ADD)
            .push_expression(1<<4)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_SUB)
            .push_expression(Self::OP_PICKSTACK())
            // At this point, we have a 256-bit number in the stack
            // Now the interesting part: the loop
            .push_expression({
                let mut script_var = Vec::new();
                // Iterating 63 times (omitting the first iteration, we have already done it)
                seq!(N in 1..64 { #(
                    let next_script = Builder::new()
                        // Extending the result to 256+4*N bits from 256*4(N-1) bits
                        .push_expression(NonNativeBigIntImpl::<{ 256 + 4*(N-1) }, 30>::OP_EXTEND::<NonNativeBigIntImpl::<{ 256 + 4*N }, 30>>())
                        // First, multiply by 16 without caring for overflow
                        .push_expression({
                            let mut script_var = Vec::new();
                            for _ in 0..4 {
                                let next_script = Builder::new()
                                    .push_expression(NonNativeBigIntImpl::<{ 256 + 4*N }, 30>::OP_2MUL_NOOVERFLOW(0))
                                    .0
                                    .into_script();
                                script_var.extend_from_slice(next_script.as_bytes());
                            }
                            Script::from(script_var)
                        })
                        // Taking coefficient, finding 16-coefficient and picking it
                        .push_opcode(OP_FROMALTSTACK)
                        .push_expression(1<<4)
                        .push_opcode(OP_SWAP)
                        .push_opcode(OP_SUB)
                        .push_expression(Self::handle_OP_PICKSTACK::<NonNativeBigIntImpl::<{ 256 + 4*N }, 30>>())
                        // Since we need to only care about last limbs,
                        // we do not extend the result
                        .push_expression(NonNativeBigIntImpl::<256, 30>::OP_ADD_NOOVERFLOW(0, 1))
                        .0
                        .into_script();
                    script_var.extend_from_slice(next_script.as_bytes());
                )* });
                Script::from(script_var)
            })
            // Moving result to the altstack
            .push_expression(U508::OP_TOALTSTACK())
            .push_expression({
                // Remvoing precomputed values from the stack
                let mut script_var = Vec::new();
                for _ in 0..1<<4 {
                    let next_script = Builder::new()
                        .push_expression(Self::OP_DROP())
                        .0
                        .into_script();
                    script_var.extend_from_slice(next_script.as_bytes());
                }
                Script::from(script_var)
            })  
            // Returning our element to the stack
            .push_expression(U508::OP_FROMALTSTACK())
            .0
            .into_script()
    }
}
