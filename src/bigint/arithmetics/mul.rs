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
}
