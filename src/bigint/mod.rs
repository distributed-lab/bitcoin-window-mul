use crate::pseudo::push_to_stack;
use crate::treepp::*;

pub mod add;
pub mod bits;
pub mod cmp;
pub mod mul;
pub mod naf;
pub mod std;
pub mod window;

pub struct BigInt<const N_BITS: usize, const LIMB_SIZE: usize> {}

impl<const N_BITS: usize, const LIMB_SIZE: usize> BigInt<N_BITS, LIMB_SIZE> {
    pub const N_BITS: usize = N_BITS;
    pub const N_LIMBS: usize = (N_BITS + LIMB_SIZE - 1) / LIMB_SIZE;
    pub const BASE: u32 = 1u32 << LIMB_SIZE;
    pub const HEAD: usize = N_BITS - (Self::N_LIMBS - 1) * LIMB_SIZE;
    pub const HEAD_OFFSET: u32 = 1u32 << Self::HEAD;

    pub fn zero() -> Script {
        push_to_stack(0, Self::N_LIMBS as usize)
    }
}

pub type U254 = BigInt<254, 30>;
pub type U64 = BigInt<64, 16>;
