use bitcoin::opcodes::all::{OP_ADD, OP_FROMALTSTACK, OP_SUB, OP_SWAP};
use bitcoin_script_stack::debugger::pushable::Builder;
use seq_macro::seq;

use crate::bigint::window::precompute::WindowedPrecomputeTable;
use crate::bigint::window::NonNativeWindowedBigIntImpl;
use crate::bigint::{U254Windowed, U254_29Windowed, U254, U254_29, U508, U508_29};
use crate::debug::print_script_size;
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
            // Note that we can simply pick the precomputed value
            // since 0*16 is still 0, so we omit the doubling :)
            OP_FROMALTSTACK 1 OP_ADD
            { 1<<WIDTH }
            OP_SWAP
            OP_SUB
            { T::OP_PICKSTACK() }

            for _ in 1..Self::DECOMPOSITION_SIZE {
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
    /// Note: this is done lazily, that is operations are from the very
    /// beginning are performed over U508.
    pub(in super::super) fn handle_lazy_OP_WIDENINGMUL<Q>() -> Script
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

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition to get twice as large integer. Chooses
    /// the most optimal method if present.
    pub(in super::super) fn handle_OP_WIDENINGMUL<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        match (Self::N_BITS, Self::LIMB_SIZE) {
            (U254::N_BITS, U254::LIMB_SIZE) => {
                NonNativeWindowedBigIntImpl::<U254, 4>::handle_optimized_OP_WIDENINGMUL()
            }
            (U254_29::N_BITS, U254_29::LIMB_SIZE) => {
                NonNativeWindowedBigIntImpl::<U254_29, 4>::handle_optimized_OP_WIDENINGMUL()
            }
            _ => Self::handle_lazy_OP_WIDENINGMUL::<Q>(),
        }
    }
}

/// Special optimized implementation for U254 Windowed method
#[allow(non_snake_case)]
impl NonNativeWindowedBigIntImpl<U254, 4> {
    /// Since copy operation requires input depth to be equal to
    /// `Self::TOP_STACK_INT_LIMBS + Self::OTHER_LIMBS * depth`, this function normalizes the depth
    /// to the required value.
    fn normalize_stack_depth<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        let n_limbs = (Q::N_BITS + Q::LIMB_SIZE - 1) / Q::LIMB_SIZE;

        script! {
            OP_DUP OP_4MUL {crate::pseudo::OP_2MUL()} // Multiplying depth by 8
            OP_ADD // Adding depth to 8*depth to get 9*depth
            { n_limbs }
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

    pub fn add_extended_to_bigger<Q: NonNativeLimbInteger>() -> Script {
        type ExtendedBy4 = NonNativeBigIntImpl<258, 30>;

        let n_limbs_other = (Q::N_BITS + Q::LIMB_SIZE - 1) / Q::LIMB_SIZE;

        use super::add::limb_add_carry;

        script! {
                { ExtendedBy4::handle_OP_ZIP(0, 1) }

                // Push the base to the stack
                { ExtendedBy4::BASE }

                // Add two limbs, take the sum to the alt stack
                limb_add_carry OP_TOALTSTACK

                for _ in 0..ExtendedBy4::N_LIMBS - 1 {
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

                // Now we have (base, carry) on the stack.
                // we sequentially add carry to the next limb, get carry back, repeat

                for _ in 0..n_limbs_other - ExtendedBy4::N_LIMBS {
                    OP_ROT // {base} {carry} {num}

                    OP_ADD // {base} {num + carry}
                    OP_2DUP OP_LESSTHANOREQUAL // {base} {num+carry} {base <= num+carry}
                    OP_TUCK // {base} {new_carry} {num+carry} {base <= num+carry}
                    OP_IF
                        2 OP_PICK OP_SUB
                    OP_ENDIF // {base} {new_carry} {sum}

                    OP_TOALTSTACK // {base} {new_carry}
                }

                OP_2DROP

                // Take all limbs from the alt stack to the main stack
                for _ in 0..n_limbs_other {
                    OP_FROMALTSTACK
                }
        }
    }

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition to get twice as large integer.
    pub(in super::super) fn handle_optimized_OP_WIDENINGMUL() -> Script {
        type ExtendedBy4 = NonNativeBigIntImpl<258, 30>;

        // The main loop script, see explanation in the returned script down below
        let main_loop_script = {
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
                    // here it's ok to use Self since U254 and U258 have the same number of limbs
                    .push_expression(Self::handle_OP_PICKSTACK::<NonNativeBigIntImpl::<{ 256 + 4*N }, 30>>())
                    // .push_expression(Self::OP_EXTEND::<NonNativeBigIntImpl<{256 + 4*N}, 30>>())
                    // .push_expression(<NonNativeBigIntImpl<{256 + 4*N}, 30>>::OP_ADD(1,0 ))
                    .push_expression(Self::add_extended_to_bigger::<NonNativeBigIntImpl<{256 + 4*N}, 30>>())
                    .0
                    .into_script();
                script_var.extend_from_slice(next_script.as_bytes());
            )* });

            Script::from(script_var)
        };

        pushable::Builder::new()
            // Push w-width form to the stack
            .push_expression(Self::OP_TOBEWINDOWEDFORM_TOALTSTACK())
            // Initialize precompute table to the stack
            // Since 256 bits fits in 9x30 limbs, we do not need
            // to extend anything, extending just in case, no overhead
            .push_expression(Self::OP_EXTEND::<ExtendedBy4>())
            .push_expression(WindowedPrecomputeTable::<ExtendedBy4, 4, true>::initialize())
            // Making the first iteration of the loop (without the initial doubling step)
            // Taking coefficient, finding 16-coefficient and picking
            // corresponding precomputed value
            .push_opcode(OP_FROMALTSTACK)
            .push_expression(1)
            .push_opcode(OP_ADD)
            .push_expression(1 << 4)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_SUB)
            // U254 and ExtendedBy4 (U258) have the same number of limbs, so it's ok
            .push_expression(Self::OP_PICKSTACK())
            // At this point, we have a 256-bit number in the stack
            // because the first window contains only 2 bits
            // Now the interesting part: the loop
            .push_expression(main_loop_script)
            // Moving result to the altstack
            .push_expression(U508::OP_TOALTSTACK())
            .push_expression({
                // Remvoing precomputed values from the stack
                let mut script_var = Vec::new();
                for _ in 0..1 << 4 {
                    let next_script = Builder::new()
                        .push_expression(ExtendedBy4::OP_DROP())
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

/// Special optimized implementation for U254 Windowed method
#[allow(non_snake_case)]
impl NonNativeWindowedBigIntImpl<U254_29, 4> {
    /// Since copy operation requires input depth to be equal to
    /// `Self::TOP_STACK_INT_LIMBS + Self::OTHER_LIMBS * depth`, this function normalizes the depth
    /// to the required value.
    fn normalize_stack_depth<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        let n_limbs = (Q::N_BITS + Q::LIMB_SIZE - 1) / Q::LIMB_SIZE;

        script! {
            OP_DUP OP_4MUL {crate::pseudo::OP_2MUL()} // Multiplying depth by 8
            OP_ADD // Adding depth to 8*depth to get 9*depth
            { n_limbs }
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

    pub fn add_extended_to_bigger<Q: NonNativeLimbInteger>() -> Script {
        type ExtendedBy4 = NonNativeBigIntImpl<258, 29>;

        let n_limbs_other = (Q::N_BITS + Q::LIMB_SIZE - 1) / Q::LIMB_SIZE;

        use super::add::limb_add_carry;

        script! {
                { ExtendedBy4::handle_OP_ZIP(0, 1) }

                // Push the base to the stack
                { ExtendedBy4::BASE }

                // Add two limbs, take the sum to the alt stack
                limb_add_carry OP_TOALTSTACK

                for _ in 0..ExtendedBy4::N_LIMBS - 1 {
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

                // Now we have (base, carry) on the stack.
                // we sequentially add carry to the next limb, get carry back, repeat

                if n_limbs_other == ExtendedBy4::N_LIMBS {
                    OP_2DROP

                    // Take all limbs from the alt stack to the main stack
                    for _ in 0..n_limbs_other {
                        OP_FROMALTSTACK
                    }
                } else {
                    for _ in 0..n_limbs_other - ExtendedBy4::N_LIMBS - 1 {
                        OP_ROT // {base} {carry} {num}

                        OP_ADD // {base} {num + carry}
                        OP_2DUP OP_LESSTHANOREQUAL // {base} {num+carry} {base <= num+carry}
                        OP_TUCK // {base} {new_carry} {num+carry} {base <= num+carry}
                        OP_IF
                            2 OP_PICK OP_SUB
                        OP_ENDIF // {base} {new_carry} {sum}

                        OP_TOALTSTACK // {base} {new_carry}
                    }

                    OP_ROT // {base} {carry} {num}

                    OP_ADD // {base} {num + carry}
                    OP_2DUP OP_LESSTHANOREQUAL // {base} {num+carry} {base <= num+carry}
                    OP_IF
                        OP_OVER OP_SUB
                    OP_ENDIF // {base} {sum}

                    OP_NIP

                    // Take all limbs from the alt stack to the main stack
                    for _ in 1..n_limbs_other {
                        OP_FROMALTSTACK
                    }
                }

        }
    }

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs
    /// using w-width decomposition to get twice as large integer.
    pub(in super::super) fn handle_optimized_OP_WIDENINGMUL() -> Script {
        type ExtendedBy4 = NonNativeBigIntImpl<258, 29>;

        // The main loop script, see explanation in the returned script down below
        let main_loop_script = {
            let mut script_var = Vec::new();
            // Iterating 63 times (omitting the first iteration, we have already done it)
            seq!(N in 1..64 { #(
                let next_script = Builder::new()
                    // Extending the result to 256+4*N bits from 256*4(N-1) bits
                    .push_expression(NonNativeBigIntImpl::<{ 256 + 4*(N-1) }, 29>::OP_EXTEND::<NonNativeBigIntImpl::<{ 256 + 4*N }, 29>>())
                    // First, multiply by 16 without caring for overflow
                    .push_expression({
                        let mut script_var = Vec::new();
                        for _ in 0..4 {
                            let next_script = Builder::new()
                             .push_expression(NonNativeBigIntImpl::<{ 256 + 4*N }, 29>::OP_2MUL_NOOVERFLOW(0))
                                .0
                                .into_script();
                            script_var.extend_from_slice(next_script.as_bytes());
                        }
                        Script::from(script_var)

                        // super::shl::shl::<NonNativeBigIntImpl::<{ 256 + 4 * N}, 29>>(4)
                        
                        // let limbs_old = (256 + 4 * (N-1) + 29 - 1) / 29;
                        // let limbs_new = (256 + 4 * N + 29 - 1) / 29;
                        // let extend = limbs_old != limbs_new;
                        // super::shl::shl4_overflowing_29(limbs_old, extend)
                    })
                    // Taking coefficient, finding 16-coefficient and picking it
                    .push_opcode(OP_FROMALTSTACK)
                    .push_expression(1<<4)
                    .push_opcode(OP_SWAP)
                    .push_opcode(OP_SUB)
                    // here it's ok to use Self since U254 and U258 have the same number of limbs
                    .push_expression(Self::handle_OP_PICKSTACK::<NonNativeBigIntImpl::<{ 256 + 4*N }, 29>>())
                    // .push_expression(Self::OP_EXTEND::<NonNativeBigIntImpl<{256 + 4*N}, 29>>())
                    // .push_expression(<NonNativeBigIntImpl<{256 + 4*N}, 29>>::OP_ADD(1,0 ))
                    .push_expression(Self::add_extended_to_bigger::<NonNativeBigIntImpl<{256 + 4*N}, 29>>())
                    .0
                    .into_script();
                script_var.extend_from_slice(next_script.as_bytes());
            )* });

            Script::from(script_var)
        };

        pushable::Builder::new()
            // Push w-width form to the stack
            .push_expression(Self::OP_TOBEWINDOWEDFORM_TOALTSTACK())
            // Initialize precompute table to the stack
            // Since 256 bits fits in 9x30 limbs, we do not need
            // to extend anything, extending just in case, no overhead
            .push_expression(Self::OP_EXTEND::<ExtendedBy4>())
            .push_expression(WindowedPrecomputeTable::<ExtendedBy4, 4, true>::initialize())
            // Making the first iteration of the loop (without the initial doubling step)
            // Taking coefficient, finding 16-coefficient and picking
            // corresponding precomputed value
            .push_opcode(OP_FROMALTSTACK)
            .push_expression(1)
            .push_opcode(OP_ADD)
            .push_expression(1 << 4)
            .push_opcode(OP_SWAP)
            .push_opcode(OP_SUB)
            // U254 and ExtendedBy4 (U258) have the same number of limbs, so it's ok
            .push_expression(Self::OP_PICKSTACK())
            // At this point, we have a 256-bit number in the stack
            // because the first window contains only 2 bits
            // Now the interesting part: the loop
            .push_expression(main_loop_script)
            // Moving result to the altstack
            .push_expression(U508_29::OP_TOALTSTACK())
            .push_expression({
                // Remvoing precomputed values from the stack
                let mut script_var = Vec::new();
                for _ in 0..1 << 4 {
                    let next_script = Builder::new()
                        .push_expression(ExtendedBy4::OP_DROP())
                        .0
                        .into_script();
                    script_var.extend_from_slice(next_script.as_bytes());
                }
                Script::from(script_var)
            })
            // Returning our element to the stack
            .push_expression(U508_29::OP_FROMALTSTACK())
            .0
            .into_script()
    }
}
