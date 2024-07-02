use super::*;

/// Trait for elements that can be decomposed into w-width windowed form.
#[allow(non_snake_case)]
pub trait Windowable {
    /// Takes the top stack big integer and outputs
    /// the low-endian w-width form in the alt stack
    fn OP_TOLEWINDOWEDFORM_TOALTSTACK() -> Script;

    /// Takes the top stack big integer and outputs
    /// the big-endian w-width form in the alt stack
    fn OP_TOBEWINDOWEDFORM_TOALTSTACK() -> Script;
}
