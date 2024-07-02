use super::*;

/// Trait for objects under which arithmetic operations can be performed.
#[allow(non_snake_case)]
pub trait Arithmeticable {
    /// Adds two [`Arithmeticable`]s on the stack at
    /// specified depths at pops them out.
    ///
    /// **Example:** `OP_ADD(0,1)` corresponds to adding the top two big integers
    fn OP_ADD(depth_1: usize, depth_2: usize) -> Script;

    /// Adds `1` to the top [`Arithmeticable`] on the stack.
    fn OP_ADD1() -> Script;

    /// Multiplies the [`Arithmeticable`] at specified depth by 2.
    ///
    /// **Example:** `OP_2MUL(0)` corresponds to multiplying the top big integer by 2.
    fn OP_2MUL(depth: usize) -> Script;

    /// Subtracts two [`Arithmeticable`]s at the specified depths.
    ///
    /// **Example:** `OP_SUB(1, 0)` corresponds to subtracting second [`Arithmeticable`] from the first one
    /// (relative to the top of the stack)
    fn OP_SUB(depth_1: usize, depth_2: usize) -> Script;

    /// Multiplies the top two [`Arithmeticable`] on the stack.
    fn OP_MUL() -> Script;
}
