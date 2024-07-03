use crate::bigint::int_extended::NonNativeExtendedBigIntImpl;
use crate::traits::integer::NonNativeLimbInteger;
use crate::treepp::*;

#[allow(non_snake_case)]
#[allow(dead_code)]
impl<T> NonNativeExtendedBigIntImpl<T> where T: NonNativeLimbInteger {
    fn handle_OP_0() -> Script {
        script! {
            // We push all zeros for each limb
            { T::OP_0() }
            { T::OP_0() }
        }
    }

    fn handle_OP_1() -> Script {
        script! {
            // The first limb is one, the rest is zero
            { T::OP_1() }
            { T::OP_0() }
        }
    }

    fn handle_OP_DROP() -> Script {
        script! {
            // We drop each of two limbs
            { T::OP_DROP() }
            { T::OP_DROP() }
        }
    }

    fn handle_OP_FROMALTSTACK() -> Script {
        script! {
            // We push each limb from the alt stack
            { T::OP_FROMALTSTACK() }
            { T::OP_FROMALTSTACK() }
        }
    }

    fn handle_OP_TOALTSTACK() -> Script {
        script! {
            // We push each limb to the alt stack
            { T::OP_TOALTSTACK() }
            { T::OP_TOALTSTACK() }
        }
    }

    fn handle_OP_ROLL(depth: usize) -> Script {
        script! {
            { T::OP_ROLL(2*depth+1) }
            { T::OP_ROLL(2*depth+1) }
        }
    }

    fn handle_OP_PICK(depth: usize) -> Script {
        script! {
            { T::OP_PICK(2*depth+1) }
            { T::OP_PICK(2*depth+1) }
        }
    }

    fn handle_OP_DUPZIP(depth: usize) -> Script {
        script! {
            { T::OP_DUPZIP(2*depth+1) }
            { T::OP_DUPZIP(2*depth+2) }
        }
    }

    fn handle_OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { T::OP_PICKZIP(2*depth_1+1, 2*depth_2+1) }
            { T::OP_PICKZIP(2*depth_1+2, 2*depth_2+2) }
        }
    }

    fn handle_OP_SWAP() -> Script {
        Self::handle_OP_ROLL(1)
    }

    fn handle_OP_ZIP(depth_1: usize, depth_2: usize) -> Script {
        script! {
            { T::OP_ZIP(2*depth_1+1, 2*depth_2+1) }
            { T::OP_ZIP(2*depth_1+2, 2*depth_2+2) }
        }
    }

    fn handle_OP_PICKSTACK() -> Script {
        unimplemented!("OP_PICKSTACK is not implemented for composed integers")
    }

    fn handle_OP_PUSH_U32LESLICE(slice: &[u32]) -> Script {
        script! {
            { T::OP_PUSH_U32LESLICE(slice) }
            { T::OP_PUSH_U32LESLICE(slice) }
        }
    }

    fn handle_OP_PUSH_DECSTR(dec_str: &str) -> Script {
        script! {
            { T::OP_PUSH_DECSTR(dec_str) }
            { T::OP_PUSH_DECSTR(dec_str) }
        }
    }

    fn handle_OP_PUSH_HEXSTR(hex_str: &str) -> Script {
        script! {
            { T::OP_PUSH_HEXSTR(hex_str) }
            { T::OP_PUSH_HEXSTR(hex_str) }
        }
    }
    
    fn handle_OP_PUSH_U64LESLICE(slice: &[u64]) -> Script {
        script! {
            { T::OP_PUSH_U64LESLICE(slice) }
            { T::OP_PUSH_U64LESLICE(slice) }
        }
    }
}