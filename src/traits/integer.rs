use super::*;
use arithmeticable::Arithmeticable;
use bitable::Bitable;
use comparable::Comparable;

/// Trait for non-native integers, which cannot
/// be represented as the Bitcoin script stack element.
///
/// It contains implementations of:
/// - Basic stack operations (copying, rolling etc.).
/// - Arithmetic operations (addition, multiplication etc.).
/// - Constants (pushing 0 and 1 to the stack).
#[allow(non_snake_case)]
pub trait NonNativeInteger: Comparable + Arithmeticable + Bitable {
    // --- Push operations ---

    /// Pushes 0 to the stack
    fn OP_0() -> Script;

    /// Pushes 1 to the stack
    fn OP_1() -> Script;

    /// Pushes the given decimal string to the stack
    fn OP_PUSH_DECSTR(dec_str: &str) -> Script;

    /// Pushes the given hex string to the stack
    fn OP_PUSH_HEXSTR(hex_str: &str) -> Script;

    /// Pushes the given [`u32`] array given in little-endian format to the stack
    /// in low-endian format (meaning, the top element in the stack contains
    /// the lowest limb).
    fn OP_PUSH_U32LESLICE(slice: &[u32]) -> Script;

    /// Pushes the given [`u64`] array given in little-endian format to the stack
    /// in big-endian format.
    fn OP_PUSH_U64LESLICE(slice: &[u64]) -> Script;

    /// Pushes the top [`NonNativeInteger`] of the stack to the alt stack.
    fn OP_TOALTSTACK() -> Script;

    /// Pushes the top [`NonNativeInteger`] of the alt stack to the main stack.
    fn OP_FROMALTSTACK() -> Script;

    /// Extends the given [`NonNativeInteger`] to the specified type.
    fn OP_EXTEND<T>() -> Script
    where
        T: NonNativeLimbInteger;

    /// Compresses the given [`NonNativeInteger`] back to the specified type.
    fn OP_COMPRESS<T>() -> Script
    where
        T: NonNativeLimbInteger;

    // --- Stack operations ---

    /// Zips two [`NonNativeInteger`]s at specified depths.
    ///
    /// **Input:** `a0,...,a{N-1},b0,...,b{N-1}`
    ///
    /// **Output:** `a0,b0,...,a{N-1},b{N-1}`
    fn OP_ZIP(depth_1: usize, depth_2: usize) -> Script;

    /// Zips the [`NonNativeInteger`] at specified depth with itself.
    ///
    /// **Input:** (`depth=0`) `a0,...,a{N-1}`
    ///
    /// **Output:** `a0,a0,...,a{N-1},a{N-1}`
    fn OP_DUPZIP(depth: usize) -> Script;

    /// Copies the [`NonNativeInteger`] at the specified depth to the top of the stack.
    fn OP_PICK(depth: usize) -> Script;

    /// Copies the [`NonNativeInteger`] at the specified depth to the top of the stack
    /// using the top element as the depth.
    fn OP_PICKSTACK() -> Script;

    /// Rolls the [`NonNativeInteger`] at the specified depth to the top of the stack.
    fn OP_ROLL(depth: usize) -> Script;

    /// Swaps top two [`NonNativeInteger`]s from the stack.
    fn OP_SWAP() -> Script;

    /// Drops the top [`NonNativeInteger`] from the stack.
    fn OP_DROP() -> Script;

    /// Picks the top two [`NonNativeInteger`]s from the stack and zips them together.
    fn OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script;
}

/// Trait for non-native integers that can be represented as a sequence of limbs.
/// Note that the only requirement is to specify the total number of limbs and the size of each limb.
#[allow(non_snake_case)]
pub trait NonNativeLimbInteger: NonNativeInteger {
    /// The total number of bits in the integer.
    const N_BITS: usize;
    /// The size of each limb in bits.
    const LIMB_SIZE: usize;
    /// The total number of limbs in the integer.
    /// 
    /// **NOTE**: This is always calculated as `(N_BITS + LIMB_SIZE - 1) / LIMB_SIZE`.
    const N_LIMBS: usize = (Self::N_BITS + Self::LIMB_SIZE - 1) / Self::LIMB_SIZE;

    /// Multiplies the top two big integers on the stack to get a big integer that is of type Q
    /// larger than the original type (for example, multiplying two 32-bit integers to get a 64-bit integer).
    fn OP_WIDENINGMUL<Q>() -> Script
    where
        Q: NonNativeLimbInteger;
}
