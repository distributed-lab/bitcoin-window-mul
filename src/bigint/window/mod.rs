use std::marker::PhantomData;

use crate::{
    traits::{
        arithmeticable::Arithmeticable,
        bitable::Bitable,
        comparable::Comparable,
        integer::{NonNativeInteger, NonNativeLimbInteger},
        window::Windowable,
    },
    treepp::*,
};

pub mod precompute;

#[cfg(test)]
pub mod test;

/// Structure representing a non-native big limb integer with the parameter
/// `WIDTH`, representing the size of the window for the windowed form
pub struct NonNativeWindowedBigIntImpl<T, const WIDTH: usize>
where
    T: NonNativeLimbInteger,
{
    _marker: PhantomData<T>,
}

impl<T, const WIDTH: usize> NonNativeWindowedBigIntImpl<T, WIDTH>
where
    T: NonNativeLimbInteger,
{
    /// Number of coefficients in the w-width form
    pub const DECOMPOSITION_SIZE: usize = get_decomposition_size(T::N_BITS, WIDTH);
}

/// Calculates the number of coefficients in the w-width form
const fn get_decomposition_size(n_bits: usize, width: usize) -> usize {
    (n_bits + width - 1) / width
}

#[allow(non_snake_case)]
impl<T: NonNativeLimbInteger, const WIDTH: usize> Windowable
    for NonNativeWindowedBigIntImpl<T, WIDTH>
{
    /// Takes the top stack big integer and outputs
    /// the low-endian w-width form in the alt stack
    #[allow(dead_code)]
    fn OP_TOLEWINDOWEDFORM_TOALTSTACK() -> Script {
        script! {
            { T::OP_TOBEBITS_TOALTSTACK() }
            { binary_to_windowed_form_toaltstack::<WIDTH>(T::N_BITS) }
        }
    }

    /// Takes the top stack big integer and outputs
    /// the big-endian w-width form in the alt stack
    fn OP_TOBEWINDOWEDFORM_TOALTSTACK() -> Script {
        script! {
            { T::OP_TOBEBITS_TOALTSTACK() }
            { binary_to_windowed_form::<WIDTH>(T::N_BITS) }

            // Moving the result to the alt stack in the reverse order
            for i in (0..Self::DECOMPOSITION_SIZE).rev() {
                {i} OP_ROLL
                OP_TOALTSTACK
            }
        }
    }
}

impl<T, const WIDTH: usize> Comparable for NonNativeWindowedBigIntImpl<T, WIDTH>
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
impl<T, const WIDTH: usize> Arithmeticable for NonNativeWindowedBigIntImpl<T, WIDTH>
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
        Self::handle_OP_MUL()
    }
}

#[allow(non_snake_case)]
impl<T, const WIDTH: usize> Bitable for NonNativeWindowedBigIntImpl<T, WIDTH>
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
impl<T, const WIDTH: usize> NonNativeInteger for NonNativeWindowedBigIntImpl<T, WIDTH>
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
}

#[allow(non_snake_case)]
impl<T, const WIDTH: usize> NonNativeLimbInteger for NonNativeWindowedBigIntImpl<T, WIDTH>
where
    T: NonNativeLimbInteger,
{
    const N_BITS: usize = T::N_BITS;
    const LIMB_SIZE: usize = T::LIMB_SIZE;
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// 3-width representation.
pub fn binary_to_windowed_form<const WIDTH: usize>(num_bits: usize) -> Script {
    // The number of coefficients in the w-width form
    let decomposition_size = get_decomposition_size(num_bits, WIDTH);
    let head_size = num_bits - (decomposition_size - 1) * WIDTH;

    // Array of chunk sizes: the last chunk may have a different size from `WIDTH`
    let chunk_sizes: Vec<_> = (0..decomposition_size)
        .map(|i| {
            if i + 1 == decomposition_size {
                return head_size;
            }

            WIDTH
        })
        .collect();

    script! {
        for size in chunk_sizes {
            // Picking top {size} bits from the stack and calculating 1<<j
            for j in 0..size {
                OP_FROMALTSTACK
                OP_IF { 1 << j } OP_ELSE { 0 } OP_ENDIF
            }

            // Adding the coefficients (we need head_size-1 add ops)
            for _ in 0..size-1 { OP_ADD }
        }
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// 3-width representation. It pushes all the coefficients to the alt stack
pub fn binary_to_windowed_form_toaltstack<const WIDTH: usize>(num_bits: usize) -> Script {
    // The number of coefficients in the w-width form
    let decomposition_size = get_decomposition_size(num_bits, WIDTH);

    script! {
        { binary_to_windowed_form::<WIDTH>(num_bits) }

        // Moving the result to the alt stack
        for _ in 0..decomposition_size {
            OP_TOALTSTACK
        }
    }
}
