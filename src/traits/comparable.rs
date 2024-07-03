use super::*;

/// Trait for elements that can be compared.
#[allow(non_snake_case)]
pub trait Comparable {
    /// Checks whether the number at specified depth
    /// is zero and removes it from the stack
    fn OP_ISZERO(depth: usize) -> Script;

    /// Verifies that two [`BigInt`]s on the stack are equal at the specified
    /// depths. For example, `OP_EQUALVERIFY(1, 0)` will verify that the top two big integers
    /// are equal. If two depths are equal, the script will be empty.
    fn OP_EQUALVERIFY(depth_1: usize, depth_2: usize) -> Script;

    /// Checks whether two [`BigInt`]s are equal at specified depths.
    /// For example, `OP_EQUAL(1, 0)` will check whether the top two big integers are equal.
    fn OP_EQUAL(depth_1: usize, depth_2: usize) -> Script;

    /// Checks whether two [`BigInt`]s are not equal.
    fn OP_NOTEQUAL(depth_1: usize, depth_2: usize) -> Script;

    /// Returns whether the [`BigInt`] at `depth_1`
    /// is less than the [`BigInt`] at `depth_2`.
    fn OP_LESSTHAN(depth_1: usize, depth_2: usize) -> Script;

    /// Returns whether the [`BigInt`] at `depth_1`
    /// is less than or equal to the [`BigInt`] at `depth_2`.
    fn OP_LESSOREQUAL(depth_1: usize, depth_2: usize) -> Script;

    /// Returns whether the [`BigInt`] at `depth_1`
    /// is greater than the [`BigInt`] at `depth_2`.
    fn OP_GREATERTHAN(depth_1: usize, depth_2: usize) -> Script;

    /// Returns whether the [`BigInt`] at `depth_1`
    /// is greater than or equal to the [`BigInt`] at `depth_2`.
    fn OP_GREATEROREQUAL(depth_1: usize, depth_2: usize) -> Script;
}
