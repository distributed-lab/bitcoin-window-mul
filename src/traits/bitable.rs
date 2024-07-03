use super::*;

/// Trait for elements that can be decomposed into binary form.
#[allow(non_snake_case)]
pub trait Bitable {
    /// Converts the [`Bitable`] to the big-endian binary form.
    fn OP_TOBEBITS() -> Script;

    /// Converts the [`Bitable`] to the little-endian binary form.
    fn OP_TOLEBITS() -> Script;

    /// Converts the [`Bitable`] to the big-endian binary form
    /// and pushes this representation to the alt stack.
    fn OP_TOBEBITS_TOALTSTACK() -> Script;

    /// Converts the [`Bitable`] to the low-endian binary form
    /// and pushes this representation to the alt stack.
    fn OP_TOLEBITS_TOALTSTACK() -> Script;
}
