use cmpeq::NonNativeCmpeqBigIntImpl;
use implementation::NonNativeBigIntImpl;
use window::NonNativeWindowedBigIntImpl;

pub mod arithmetics;
pub mod bits;
pub mod cmpeq;
pub mod comparison;
pub mod naf;
pub mod stack;
pub mod window;

pub mod implementation;

/// Type alias for a 254-bit non-native big integer.
pub type U254 = NonNativeBigIntImpl<254, 30>;
/// Type alias for a 255-bit non-native big integer, represented by 17 15-byte limbs.
pub type U255 = NonNativeBigIntImpl<255, 15>;
/// Type alias for a 255-bit non-native big integer implementation using
/// cmpeq's implementation: https://bitcointalk.org/index.php?topic=5477449.0.
pub type U255Cmpeq = NonNativeCmpeqBigIntImpl<U255>;
/// Type alias for a 254-bit non-native big integer with window size of 4.
pub type U254Windowed = NonNativeWindowedBigIntImpl<U254, 4>;
/// Type alias for a 64-bit non-native big integer.
pub type U64 = NonNativeBigIntImpl<64, 16>;
/// Type alias for a 508-bit non-native big integer.
pub type U508 = NonNativeBigIntImpl<508, 30>;
/// Type alias for a 512-bit non-native big integer.
pub type U510 = NonNativeBigIntImpl<510, 15>;

/// Type alias for a 254-bit non-native big integer. Equivalent to the one used in bitvm.
pub type U254_29 = NonNativeBigIntImpl<254, 29>;
/// Type alias for a 254-bit non-native big integer with window size of 4.
pub type U254_29Windowed = NonNativeWindowedBigIntImpl<U254_29, 4>;
/// Type alias for a 508-bit non-native big integer. Equivalent to the one used in bitvm.
pub type U508_29 = NonNativeBigIntImpl<508, 29>;

#[cfg(test)]
pub mod performance;
