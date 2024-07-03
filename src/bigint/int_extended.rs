use super::*;
use ::std::marker::PhantomData;

// TODO: Make extended big int generic over the number of limbs

/// Structure representing an extented [`NonNativeLimbInteger`] composed
/// of two (lower and higher) limbs.
pub struct NonNativeExtendedBigIntImpl<T> 
where T: NonNativeLimbInteger {
    _marker: PhantomData<T>,
}

impl<T> NonNativeExtendedBigIntImpl<T>
where T: NonNativeLimbInteger {
    pub const N_BITS: usize = 2 * T::N_BITS;
    pub const LIMB_SIZE: usize = T::LIMB_SIZE;
}

