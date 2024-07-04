use std::marker::PhantomData;

use crate::{
    bigint::U510,
    script_loader::AsmScriptLoader,
    traits::{
        arithmeticable::Arithmeticable,
        bitable::Bitable,
        comparable::Comparable,
        integer::{NonNativeInteger, NonNativeLimbInteger},
    },
    treepp::*,
};

#[cfg(test)]
pub mod test;

/// Structure representing a non-native big limb integer which is implemented
/// using cmpeq's implementation, which can be read here:
/// https://bitcointalk.org/index.php?topic=5477449.0
pub struct NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    _marker: PhantomData<T>,
}

impl<'a, T> NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    pub const WIDENINGMUL_SCRIPT: &'a str = include_str!("bigint255_mul15_x17.asm");
}

impl<T> Comparable for NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    fn OP_EQUAL(depth_1: usize, depth_2: usize) -> Script {
        T::OP_EQUAL(depth_1, depth_2)
    }
    fn OP_EQUALVERIFY(depth_1: usize, depth_2: usize) -> Script {
        T::OP_EQUALVERIFY(depth_1, depth_2)
    }
    fn OP_GREATEROREQUAL(depth_1: usize, depth_2: usize) -> Script {
        T::OP_GREATEROREQUAL(depth_1, depth_2)
    }
    fn OP_GREATERTHAN(depth_1: usize, depth_2: usize) -> Script {
        T::OP_GREATERTHAN(depth_1, depth_2)
    }
    fn OP_ISZERO(depth: usize) -> Script {
        T::OP_ISZERO(depth)
    }
    fn OP_LESSOREQUAL(depth_1: usize, depth_2: usize) -> Script {
        T::OP_LESSOREQUAL(depth_1, depth_2)
    }
    fn OP_LESSTHAN(depth_1: usize, depth_2: usize) -> Script {
        T::OP_LESSTHAN(depth_1, depth_2)
    }
    fn OP_NOTEQUAL(depth_1: usize, depth_2: usize) -> Script {
        T::OP_NOTEQUAL(depth_1, depth_2)
    }
}

#[allow(non_snake_case)]
impl<T> Arithmeticable for NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    fn OP_2MUL(depth: usize) -> Script {
        T::OP_2MUL(depth)
    }
    fn OP_ADD(depth_1: usize, depth_2: usize) -> Script {
        T::OP_ADD(depth_1, depth_2)
    }
    fn OP_SUB(depth_1: usize, depth_2: usize) -> Script {
        T::OP_SUB(depth_1, depth_2)
    }
    fn OP_ADD1() -> Script {
        T::OP_ADD1()
    }
    fn OP_MUL() -> Script {
        T::OP_MUL()
    }
}

#[allow(non_snake_case)]
impl<T> Bitable for NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    fn OP_TOBEBITS() -> Script {
        T::OP_TOBEBITS()
    }
    fn OP_TOBEBITS_TOALTSTACK() -> Script {
        T::OP_TOBEBITS_TOALTSTACK()
    }
    fn OP_TOLEBITS() -> Script {
        T::OP_TOLEBITS()
    }
    fn OP_TOLEBITS_TOALTSTACK() -> Script {
        T::OP_TOLEBITS_TOALTSTACK()
    }
}

#[allow(non_snake_case)]
impl<T> NonNativeInteger for NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    fn OP_0() -> Script {
        T::OP_0()
    }
    fn OP_1() -> Script {
        T::OP_1()
    }
    fn OP_DROP() -> Script {
        T::OP_DROP()
    }
    fn OP_DUPZIP(depth: usize) -> Script {
        T::OP_DUPZIP(depth)
    }
    fn OP_FROMALTSTACK() -> Script {
        T::OP_FROMALTSTACK()
    }
    fn OP_PICK(depth: usize) -> Script {
        T::OP_PICK(depth)
    }
    fn OP_PICKSTACK() -> Script {
        T::OP_PICKSTACK()
    }
    fn OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script {
        T::OP_PICKZIP(depth_1, depth_2)
    }
    fn OP_PUSH_DECSTR(dec_str: &str) -> Script {
        T::OP_PUSH_DECSTR(dec_str)
    }
    fn OP_PUSH_HEXSTR(hex_str: &str) -> Script {
        T::OP_PUSH_HEXSTR(hex_str)
    }
    fn OP_PUSH_U32LESLICE(slice: &[u32]) -> Script {
        T::OP_PUSH_U32LESLICE(slice)
    }
    fn OP_PUSH_U64LESLICE(slice: &[u64]) -> Script {
        T::OP_PUSH_U64LESLICE(slice)
    }
    fn OP_ROLL(depth: usize) -> Script {
        T::OP_ROLL(depth)
    }
    fn OP_SWAP() -> Script {
        T::OP_SWAP()
    }
    fn OP_TOALTSTACK() -> Script {
        T::OP_TOALTSTACK()
    }
    fn OP_ZIP(depth_1: usize, depth_2: usize) -> Script {
        T::OP_ZIP(depth_1, depth_2)
    }
    fn OP_EXTEND<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        T::OP_EXTEND::<Q>()
    }
}

#[allow(non_snake_case)]
impl<T> NonNativeLimbInteger for NonNativeCmpeqBigIntImpl<T>
where
    T: NonNativeLimbInteger,
{
    const N_BITS: usize = T::N_BITS;
    const LIMB_SIZE: usize = T::LIMB_SIZE;

    /// NOTE: only extension to U510 is supported!
    fn OP_WIDENINGMUL<Q>() -> Script
    where
        Q: NonNativeLimbInteger,
    {
        assert_eq!(
            Q::N_BITS,
            U510::N_BITS,
            "only extension to u510 is supported"
        );
        AsmScriptLoader::from_str(Self::WIDENINGMUL_SCRIPT)
    }
}
