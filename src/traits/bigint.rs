use super::*;
use comparable::Comparable;

/// Trait for big integers, containing the main logic for
/// operating with big integers. Namely, it contains implementations of:
/// - Basic stack operations (copying, rolling etc.).
/// - Arithmetic operations (addition, multiplication etc.).
/// - Constants (pushing 0 and 1 to the stack).
#[allow(non_snake_case)]
pub trait BigInt: Comparable {
    // --- Push operations ---

    /// Pushes 0 to the stack
    fn OP_0() -> Script;

    /// Pushes 1 to the stack
    fn OP_1() -> Script;

    /// Pushes the given decimal string to the stack
    fn OP_PUSHDECSTR(dec_str: &str) -> Script;

    /// Pushes the given hex string to the stack
    fn OP_PUSHHEXSTR(hex_str: &str) -> Script;

    /// Pushes the given u32 array given in little-endian format to the stack
    /// in low-endian format (meaning, the top element in the stack contains
    /// the lowest limb).
    fn OP_PUSHU32LESLICE(slice: &[u32]) -> Script;

    /// Pushes the given u64 array given in little-endian format to the stack
    /// in big-endian format.
    fn OP_PUSHU64LESLICE(slice: &[u64]) -> Script;

    /// Pushes the top element of the stack to the alt stack.
    fn OP_TOALTSTACK() -> Script;

    /// Pushes the top element of the alt stack to the main stack.
    fn OP_FROMALTSTACK() -> Script;

    // --- Stack operations ---

    /// Zips two elements at specified depths.
    ///
    /// **Input:** `a0,...,a{N-1},b0,...,b{N-1}`
    ///
    /// **Output:** `a0,b0,...,a{N-1},b{N-1}`
    fn OP_ZIP(depth_1: usize, depth_2: usize) -> Script;

    /// Zips the element at specified depth with itself.
    ///
    /// **Input:** (`depth=0`) `a0,...,a{N-1}`
    ///
    /// **Output:** `a0,a0,...,a{N-1},a{N-1}`
    fn OP_DUPZIP(depth: usize) -> Script;

    /// Copies the element at the specified depth to the top of the stack.
    fn OP_PICK(depth: usize) -> Script;

    /// Copies the element at the specified depth to the top of the stack
    /// using the top element as the depth.
    fn OP_PICKSTACK() -> Script;

    /// Rolls the element at the specified depth to the top of the stack.
    fn OP_ROLL(depth: usize) -> Script;

    /// Swaps top two `BigInt`s from the stack.
    fn OP_SWAP() -> Script;

    /// Drops the top `BigInt` from the stack.
    fn OP_DROP() -> Script;

    /// Picks the top two `BigInt`s from the stack and zips them together.
    fn OP_PICKZIP(depth_1: usize, depth_2: usize) -> Script;

    // --- Arithmetic operations ---

    /// Adds two [`BigInt`]s on the stack at
    /// specified depths.
    ///
    /// **Example:** `OP_ADD(0,1)` corresponds to adding the top two big integers
    fn OP_ADD(depth_1: usize, depth_2: usize) -> Script;

    /// Adds 1 to the top [`BigInt`] on the stack.
    fn OP_ADD1() -> Script;

    /// Multiplies the [`BigInt`] at specified depth by 2.
    ///
    /// **Example:** `OP_2MUL(0)` corresponds to multiplying the top big integer by 2.
    fn OP_2MUL(depth: usize) -> Script;

    /// Subtracts two [`BigInt`]s at the specified depths.
    ///
    /// **Example:** `OP_SUB(1, 0)` corresponds to subtracting second integer from the first one
    /// (relative to the top of the stack)
    fn OP_SUB(depth_1: usize, depth_2: usize) -> Script;

    /// Multiplies the top two big integers on the stack
    /// represented as little-endian 32-bit limbs using
    /// binary decomposition.
    fn OP_MUL() -> Script;
}
