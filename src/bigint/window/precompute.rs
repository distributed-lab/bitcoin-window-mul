use std::marker::PhantomData;

use crate::traits::integer::NonNativeLimbInteger;
use crate::treepp::*;

pub struct WindowedPrecomputeTable<T, const WIDTH: usize, const NOOVERFLOW: bool>
where
    T: NonNativeLimbInteger,
{
    _marker: PhantomData<T>,
}

#[allow(non_snake_case)]
impl<T, const WIDTH: usize, const NOOVERFLOW: bool> WindowedPrecomputeTable<T, WIDTH, NOOVERFLOW>
where
    T: NonNativeLimbInteger,
{
    /// Chooses the correct `OP_2MUL` operation based on the `NOOVERFLOW` flag
    /// and returns the corresponding script.
    fn OP_2MUL(depth: usize) -> Script {
        if NOOVERFLOW {
            return T::OP_2MUL_NOOVERFLOW(0);
        }

        T::OP_2MUL(depth)
    }

    /// Chooses the correct `OP_ADD` operation based on the `NOOVERFLOW` flag
    /// and returns the corresponding script.
    fn OP_ADD(depth_1: usize, depth_2: usize) -> Script {
        if NOOVERFLOW {
            return T::OP_ADD_NOOVERFLOW(depth_1, depth_2);
        }

        T::OP_ADD(depth_1, depth_2)
    }

    /// Precomputes values `{0*z, 1*z, 2*z}` (corresponding to `WIDTH=2`) needed
    /// for multiplication, assuming that `z` is the top stack element.
    fn precompute_012_mul() -> Script {
        script! {
            { T::OP_0() }       // {z, 0}
            { T::OP_SWAP() }    // {0, z}
            { T::OP_PICK(0) }   // {0, z, z}
            { Self::OP_2MUL(0) }   // {0, z, 2*z}
        }
    }

    /// Precomputes values `{0*z, 1*z, 2*z, 3*z}` (corresponding to `WIDTH=2`) needed
    /// for multiplication, assuming that `z` is the top stack element.
    fn precompute_2_mul() -> Script {
        script! {
            { Self::precompute_012_mul() }
            { T::OP_PICK(1) }   // {0, z, 2*z, z}
            { T::OP_PICK(1) }   // {0, z, 2*z, z, 2*z}
            { Self::OP_ADD(0, 1) } // {0, z, 2*z, 3*z}
        }
    }

    /// Precomputes values `{0*z, 1*z, ..., 7*z}` (corresponding to `WIDTH=3`) needed
    /// for multiplication, assuming that `z` is the top stack element.
    fn precompute_3_mul() -> Script {
        script! {
            { Self::precompute_2_mul() }
            { T::OP_PICK(1) }    // {0, z, 2*z, 3*z, 2*z}
            { Self::OP_2MUL(0) }    // {0, z, 2*z, 3*z, 4*z}
            { T::OP_PICK(3) }    // {0, z, 2*z, 3*z, 4*z, z}
            { T::OP_PICK(1) }    // {0, z, 2*z, 3*z, 4*z, z, 4*z}
            { Self::OP_ADD(0, 1) }  // {0, z, 2*z, 3*z, 4*z, 5*z}
            { T::OP_PICK(2) }    // {0, z, 2*z, 3*z, 4*z, 5*z, 3*z}
            { Self::OP_2MUL(0) }    // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z}
            { T::OP_PICK(5) }    // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, z}
            { T::OP_PICK(1) }    // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, z, 6*z}
            { Self::OP_ADD(0, 1) }  // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z}
        }
    }

    /// Precomputes values `{0*z, 1*z, ..., 7*z, ..., 14*z, 15*z}` (corresponding to `WIDTH=4`) needed
    /// for multiplication, assuming that `z` is the top stack element.
    fn precompute_4_mul() -> Script {
        script! {
            { Self::precompute_3_mul() } // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z}
            { T::OP_PICK(3) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 4*z}
            { Self::OP_2MUL(0) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z}
            { T::OP_PICK(7) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, z}
            { T::OP_PICK(1) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, z, 8*z}
            { Self::OP_ADD(1, 0) }          // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z}
            { T::OP_PICK(4) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 5*z}
            { Self::OP_2MUL(0) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z}
            { T::OP_PICK(9) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, z}
            { T::OP_PICK(1) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, z, 10*z}
            { Self::OP_ADD(1, 0) }          // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z}
            { T::OP_PICK(5) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 6*z}
            { Self::OP_2MUL(0) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z}
            { T::OP_PICK(11) }           // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, z}
            { T::OP_PICK(1) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, z, 12*z}
            { Self::OP_ADD(1, 0) }          // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z}
            { T::OP_PICK(6) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z, 7*z}
            { Self::OP_2MUL(0) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z, 14*z}
            { T::OP_PICK(13) }           // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z, 14*z, z}
            { T::OP_PICK(1) }            // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z, 14*z, z, 14*z}
            { Self::OP_ADD(1, 0) }          // {0, z, 2*z, 3*z, 4*z, 5*z, 6*z, 7*z, 8*z, 9*z, 10*z, 11*z, 12*z, 13*z, 14*z, 15*z}
        }
    }

    /// Precomputes values `{0*z, 1*z, 2*z, ..., 2^(WIDTH)-1}` needed for
    /// multiplication, assuming that `z` is the top stack element. However,
    /// this is done lazily, costing `1` doubling and `2^(WIDTH-3)` additions, which
    /// can be done more optimally using more doublings => less additions.
    pub fn lazy_initialize() -> Script {
        assert!(WIDTH >= 2, "width should be at least 2");

        script! {
            { Self::precompute_012_mul() } // Precomputing {0, z, 2*z}
            for i in 0..(1<<WIDTH)-3 {
                // Given {0, z, 2z, ..., (i+2)z} we add (i+3)z to the end
                { T::OP_PICK(0) }   // {0, z, ..., (i+2)z, (i+2)z}
                { T::OP_PICK(i+2) } // {0, z, ..., (i+2)z, (i+2)z, z}
                { Self::OP_ADD(0, 1) } // {0, z, ..., (i+2)z, (i+3)z}
            }
        }
    }

    /// Precomputes values `{0*z, 1*z, 2*z, ..., 2^(WIDTH)-1}` needed for
    /// multiplication, assuming that `z` is the top stack element. The method
    /// is well-optimized for `WIDTH <= 4`.
    pub fn initialize() -> Script {
        assert!(WIDTH >= 2, "width should be at least 2");

        match WIDTH {
            2 => Self::precompute_2_mul(),
            3 => Self::precompute_3_mul(),
            4 => Self::precompute_4_mul(),
            _ => Self::lazy_initialize(),
        }
    }
}
