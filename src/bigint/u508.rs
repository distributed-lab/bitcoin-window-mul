use super::*;
use ::std::marker::PhantomData;

pub struct ComposedBigInt<T: NonNativeInteger, const LIMB_NUM: usize> {
    _marker: PhantomData<T>,
}

pub type U508 = ComposedBigInt<U254, 2>;
