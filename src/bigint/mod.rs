use implementation::NonNativeBigIntImpl;
use window::NonNativeWindowedBigIntImpl;

pub mod arithmetics;
pub mod bits;
pub mod comparison;
pub mod naf;
pub mod stack;
pub mod window;

pub mod implementation;
pub mod performance;

/// Type alias for a 254-bit non-native big integer.
pub type U254 = NonNativeBigIntImpl<254, 30>;
/// Type alias for a 254-bit non-native big integer with window size of 4.
pub type U254Windowed = NonNativeWindowedBigIntImpl<U254, 4>;
/// Type alias for a 64-bit non-native big integer.
pub type U64 = NonNativeBigIntImpl<64, 16>;
/// Type alias for a 508-bit non-native big integer.
pub type U508 = NonNativeBigIntImpl<508, 30>;
