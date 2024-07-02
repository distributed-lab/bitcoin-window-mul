use super::*;
use ::std::marker::PhantomData;

pub struct NonNativeComposedBigIntImpl<T: NonNativeInteger, const LIMB_NUM: usize> {
    _marker: PhantomData<T>,
}
