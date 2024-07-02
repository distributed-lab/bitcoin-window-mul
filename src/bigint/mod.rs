use window::NonNativeWindowedBigIntImpl;

use crate::{
    traits::{
        arithmeticable::Arithmeticable,
        bitable::Bitable,
        comparable::Comparable,
        integer::{NonNativeInteger, NonNativeLimbInteger},
    },
    treepp::*,
};

pub mod arithmetics;
pub mod bits;
pub mod comparison;
pub mod window;

pub mod naf;
pub mod std;
pub mod u508;

/// Structure representing a non-native big integer with `N_BITS` bits and `LIMB_SIZE` bits per limb
/// implementing the [`NonNativeBigInt`] trait.
pub struct NonNativeBigIntImpl<const N_BITS: usize, const LIMB_SIZE: usize> {}

impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeLimbInteger
    for NonNativeBigIntImpl<N_BITS, LIMB_SIZE>
{
    const LIMB_SIZE: usize = LIMB_SIZE;
    const N_BITS: usize = N_BITS;
}

impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigIntImpl<N_BITS, LIMB_SIZE> {
    /// Number of bits per limb
    const N_LIMBS: usize = (N_BITS + LIMB_SIZE - 1) / LIMB_SIZE;
    /// Base of the big integer is u32
    const BASE: u32 = 1u32 << LIMB_SIZE;
    /// Numbers of bits in the head limb
    const HEAD: usize = N_BITS - (Self::N_LIMBS - 1) * LIMB_SIZE;
    /// Head maximum value + 1
    const HEAD_OFFSET: u32 = 1u32 << Self::HEAD;
}

impl<const N_BITS: usize, const LIMB_SIZE: usize> Comparable
    for NonNativeBigIntImpl<N_BITS, LIMB_SIZE>
{
    fn OP_EQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_EQUAL(depth_1, depth_2)
    }
    fn OP_EQUALVERIFY(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_EQUALVERIFY(depth_1, depth_2)
    }
    fn OP_ISZERO(depth: usize) -> Script {
        Self::handle_OP_ISZERO(depth)
    }
    fn OP_GREATEROREQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_GREATEROREQUAL(depth_1, depth_2)
    }
    fn OP_GREATERTHAN(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_GREATERTHAN(depth_1, depth_2)
    }
    fn OP_LESSOREQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_LESSOREQUAL(depth_1, depth_2)
    }
    fn OP_LESSTHAN(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_LESSTHAN(depth_1, depth_2)
    }
    fn OP_NOTEQUAL(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_NOTEQUAL(depth_1, depth_2)
    }
}

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> Arithmeticable
    for NonNativeBigIntImpl<N_BITS, LIMB_SIZE>
{
    fn OP_ADD(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_ADD(depth_1, depth_2)
    }
    fn OP_ADD1() -> Script {
        Self::handle_OP_ADD1()
    }
    fn OP_SUB(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_SUB(depth_1, depth_2)
    }
    fn OP_2MUL(depth: usize) -> Script {
        Self::handle_OP_2MUL(depth)
    }
    fn OP_MUL() -> Script {
        Self::handle_OP_MUL()
    }
}

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> Bitable
    for NonNativeBigIntImpl<N_BITS, LIMB_SIZE>
{
    fn OP_TOBEBITS() -> Script {
        Self::handle_OP_TOBEBITS()
    }
    fn OP_TOLEBITS() -> Script {
        Self::handle_OP_TOLEBITS()
    }
    fn OP_TOBEBITS_TOALTSTACK() -> Script {
        Self::handle_OP_TOBEBITS_TOALTSTACK()
    }
    fn OP_TOLEBITS_TOALTSTACK() -> Script {
        Self::handle_OP_TOLEBITS_TOALTSTACK()
    }
}

#[allow(non_snake_case)]
impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeInteger
    for NonNativeBigIntImpl<N_BITS, LIMB_SIZE>
{
    fn OP_0() -> Script {
        Self::handle_OP_0()
    }
    fn OP_1() -> Script {
        Self::handle_OP_1()
    }
    fn OP_PUSH_DECSTR(dec_str: &str) -> Script {
        Self::handle_OP_PUSHDECSTR(dec_str)
    }
    fn OP_PUSH_HEXSTR(hex_str: &str) -> Script {
        Self::handle_OP_PUSHHEX(hex_str)
    }
    fn OP_DROP() -> Script {
        Self::handle_OP_DROP()
    }
    fn OP_FROMALTSTACK() -> Script {
        Self::handle_OP_FROMALTSTACK()
    }
    fn OP_TOALTSTACK() -> Script {
        Self::handle_OP_TOALTSTACK()
    }
    fn OP_PICK(depth: usize) -> Script {
        Self::handle_OP_PICK(depth)
    }
    fn OP_PICKSTACK() -> Script {
        Self::handle_OP_PICKSTACK()
    }
    fn OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_PICKZIP(depth_1, depth_2)
    }
    fn OP_PUSH_U32LESLICE(slice: &[u32]) -> Script {
        Self::handle_OP_PUSHU32LESLICE(slice)
    }
    fn OP_PUSH_U64LESLICE(slice: &[u64]) -> Script {
        Self::handle_OP_PUSHU64LESLICE(slice)
    }
    fn OP_ROLL(depth: usize) -> Script {
        Self::handle_OP_ROLL(depth)
    }
    fn OP_SWAP() -> Script {
        Self::handle_OP_SWAP()
    }
    fn OP_ZIP(depth_1: usize, depth_2: usize) -> Script {
        Self::handle_OP_ZIP(depth_1, depth_2)
    }
    fn OP_DUPZIP(depth: usize) -> Script {
        Self::handle_OP_DUPZIP(depth)
    }
}

pub type U254 = NonNativeBigIntImpl<254, 30>;
pub type U254Windowed = NonNativeWindowedBigIntImpl<U254, 4>;
pub type U64 = NonNativeBigIntImpl<64, 16>;
