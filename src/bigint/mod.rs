use int_extended::NonNativeExtendedBigIntImpl;
use int_simple::NonNativeBigIntImpl;
use window::NonNativeWindowedBigIntImpl;
use crate::traits::integer:: NonNativeLimbInteger;

pub mod arithmetics;
pub mod bits;
pub mod comparison;
pub mod window;
pub mod naf;
pub mod stack;

pub mod int_simple;
pub mod int_extended;
pub mod performance;

/// Type alias for a 254-bit non-native big integer.
pub type U254 = NonNativeBigIntImpl<254, 30>;
/// Type alias for a 254-bit non-native big integer with window size of 4.
pub type U254Windowed = NonNativeWindowedBigIntImpl<U254, 4>;
/// Type alias for a 64-bit non-native big integer.
pub type U64 = NonNativeBigIntImpl<64, 16>;
/// Type alias for a 508-bit non-native big integer.
pub type U508 = NonNativeExtendedBigIntImpl<U254>;