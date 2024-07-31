use crate::traits::integer::NonNativeLimbInteger;
use crate::treepp::{pushable, script, Script};

// a -> ( a << n ) ( a >> (LIMB_SIZE - n) )
// n = 8, LIMB_SIZE = 24 => 0xFFFFFF -> 0xFFFF00 0xFF
fn limb_widening_shl<T: NonNativeLimbInteger>(n: usize) -> Script {
    assert!(
        (0..T::LIMB_SIZE).contains(&n),
        "limb_widening_shl accepts only parameters in 1..LIMB_SIZE"
    );

    if n == 0 {
        script! {
            OP_0
        }
    } else {
        script! {
            { 1 << T::LIMB_SIZE }
            OP_SWAP

            // shift by one bit n times
            for _ in 0..n {
                // 2^LIMB_SIZE num
                OP_DUP OP_ADD // 2^LIMB_SIZE 2num
                OP_2DUP OP_LESSTHANOREQUAL // 2^LIMB_SIZE 2num 2^LIMB_SIZE<=2num
                OP_DUP OP_TOALTSTACK // 2^LIMB_SIZE 2num 2^LIMB_SIZE<=2num (bit is put on the alt stack)
                OP_IF
                    OP_OVER OP_SUB
                OP_ENDIF
                // 2^LIMB_SIZE clamp(2num)
            }

            OP_NIP // rest

            for _ in 0..n {
                OP_FROMALTSTACK
            }

            for _ in 1..n {
                OP_DUP OP_ADD OP_ADD
            }
        }
    }
}

fn limb_overflowing_shl<T: NonNativeLimbInteger>(n: usize) -> Script {
    assert!(
        (0..T::LIMB_SIZE).contains(&n),
        "limb_overflowing_shl accepts only parameters in 1..LIMB_SIZE"
    );

    if n == 0 {
        script! {}
    } else {
        script! {
            { 1 << T::LIMB_SIZE }
            OP_SWAP

            // shift by one bit n times and drop bit
            for _ in 0..n {
                // 2^LIMB_SIZE num
                OP_DUP OP_ADD // 2^LINB_SIZE 2num
                OP_2DUP OP_LESSTHANOREQUAL // 2^LIMB_SIZE 2num 2^LIMB_SIZE<=2num
                OP_IF
                    OP_OVER OP_SUB
                OP_ENDIF
                // 2^LIMB_SIZE clamp(2num)
            }

            OP_NIP
        }
    }
}

fn limb_overflowing_shl_unchecked(n: usize) -> Script {
    script! {
        // shift by one bit n times without checking
        for _ in 0..n {
            OP_DUP OP_ADD // 2num
        }
    }
}

fn head_shl<T: NonNativeLimbInteger>(n: usize) -> Script {
    let limb_n = (T::N_BITS + T::LIMB_SIZE - 1) / T::LIMB_SIZE;
    let head = T::N_BITS - (limb_n - 1) * T::LIMB_SIZE;

    assert!(
        (1..head).contains(&n),
        "head_shl accepts only parameters in 1..head"
    );

    script! {
        { 1 << head }
        OP_SWAP

        // shift by one bit n times and drop bit
        for _ in 0..n {
            // 2^head num
            OP_DUP OP_ADD // 2^head 2num
            OP_2DUP OP_LESSTHANOREQUAL // 2^head 2num 2^head<=2num
            OP_IF
                OP_OVER OP_SUB
            OP_ENDIF
            // 2^head clamp(2num)
        }

        OP_NIP
    }
}

fn drop_bits(from: usize, to: usize) -> Script {
    assert!(from >= to, "bits must be dropped from higher to lower");

    script! {
        for i in 0..from - to {
            { 1 << (from - i - 1) } // num clamping
            OP_2DUP OP_GREATERTHANOREQUAL // num clamning num>=clamping
            OP_IF
                OP_SUB
            OP_ELSE
                OP_DROP
            OP_ENDIF
        }
    }
}

fn limb_to_head<T: NonNativeLimbInteger>() -> Script {
    let limb_n = (T::N_BITS + T::LIMB_SIZE - 1) / T::LIMB_SIZE;
    let head = T::N_BITS - (limb_n - 1) * T::LIMB_SIZE;

    drop_bits(T::LIMB_SIZE, head)
}

pub fn shl<T: NonNativeLimbInteger>(n: usize) -> Script {
    let limbs_n = (T::N_BITS + T::LIMB_SIZE - 1) / T::LIMB_SIZE;
    let head = T::N_BITS - (limbs_n - 1) * T::LIMB_SIZE;

    if n < head {
        // no need to drop limbs
        script! {
            // move body to altstack
            for _ in 0..limbs_n - 1 {
                OP_TOALTSTACK
            }

            { head_shl::<T>(n) }

            for _ in 0..limbs_n - 1 {
                OP_FROMALTSTACK

                { limb_widening_shl::<T>(n) } // prev bottom top

                OP_ROT OP_ADD OP_SWAP // prev+top bottom
            }

        }
    } else {
        // at least one limb is droped

        let limbs_to_drop = 1 + (n - head) / T::LIMB_SIZE;
        let limbs_to_keep = limbs_n - limbs_to_drop;

        let bits_in_first_limb_to_keep =
            T::LIMB_SIZE - (n - head - (limbs_to_drop - 1) * T::LIMB_SIZE);

        let extend_first_limb = head < bits_in_first_limb_to_keep;

        let shift_amt = if !extend_first_limb {
            head - bits_in_first_limb_to_keep
        } else {
            T::LIMB_SIZE - (bits_in_first_limb_to_keep - head)
        };

        let limbs_to_add = if extend_first_limb {
            limbs_to_drop - 1
        } else {
            limbs_to_drop
        };

        script! {
            for _ in 0..limbs_to_keep {
                OP_TOALTSTACK
            }
            for _ in 0..limbs_to_drop {
                OP_DROP
            }

            // get top element, shift and clamp
            OP_FROMALTSTACK
            if extend_first_limb {
                { limb_widening_shl::<T>(shift_amt) } // bottom top
                { drop_bits(shift_amt, head) } // bottom clamp(top)
                OP_SWAP
            } else {
                { drop_bits(T::LIMB_SIZE, head - shift_amt) } // clamp(top)
                { limb_overflowing_shl::<T>(shift_amt) } // head_adjusted_top
            }

            // shift left limbs
            for _ in 0..limbs_to_keep - 1 {
                OP_FROMALTSTACK

                { limb_widening_shl::<T>(shift_amt) } // prev bottom top

                OP_ROT OP_ADD OP_SWAP // prev+top bottom
            }

            // fill rest with 0s
            for _ in 0..limbs_to_add {
                OP_0
            }
        }
    }
}

pub fn shl4_overflowing_29(n_limbs: usize, extending: bool) -> Script {
    use crate::bigint::U254_29;

    script! {
        for _ in 1..n_limbs {
            OP_TOALTSTACK
        }

        if extending {
            { limb_widening_shl::<U254_29>(4) } // type is only used to determine limb size
            OP_SWAP // top bottom
        } else {
            { limb_overflowing_shl_unchecked(4) }
        }

        for _ in 1..n_limbs {
            OP_FROMALTSTACK // left limb
            { limb_widening_shl::<U254_29>(4) } // left bottom top
            OP_ROT OP_ADD OP_SWAP // left+top bottom
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bigint::U254_29;
    use crate::debug::execute_script;
    use crate::traits::comparable::Comparable;
    use crate::traits::integer::NonNativeInteger;
    use num_bigint::BigUint;
    use num_traits::Num;

    #[test]
    fn test_limb_widening_shl() {
        let script = script! {
            { 0b1_1001_1101_1001_1111_0000_1010_0101 }
            { limb_widening_shl::<U254_29>(17) }
            { 0b0_0000_0000_0001_1001_1101_1001_1111 } OP_EQUALVERIFY
            { 0b0_0001_0100_1010_0000_0000_0000_0000 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_limb_overflowing_shl() {
        let script = script! {
            { 0b0_1011_1101_1001_1111_0000_1010_0101 }
            { limb_overflowing_shl::<U254_29>(7) }
            { 0b0_1100_1111_1000_0101_0010_1000_0000 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_drop_bits() {
        let script = script! {
            { 0b001_1111_0000_1010_0101 }
            { drop_bits(19, 13) }
            {        0b1_0000_1010_0101 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_limb_to_head() {
        let script = script! {
            { 0b1_1101_1001_1001_1111_0000_1010_0101 }
            { limb_to_head::<U254_29>() }
            {          0b01_1001_1111_0000_1010_0101 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_head_shl() {
        let script = script! {
            { 0b01_1001_1111_0000_1010_0101 }
            { head_shl::<U254_29>(5) }
            { 0b11_1110_0001_0100_1010_0000 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    #[test]
    fn test_shl_long() {
        let num = BigUint::from_str_radix(
"11111000100010011110011010111101010011010011110101010111110000111110100111000000001101001010011000010011001010011100111001110110100100010001110100111000110001011111111001011101011100100001100011110101011011000100001001011010000011101001111100111110111011", 2).unwrap();

        for i in 1..100 {
            let shifted: BigUint = num.clone() << i;

            let script = script! {
                { U254_29::OP_PUSH_U32LESLICE(&num.to_u32_digits()) }
                { shl::<U254_29>(i) }
                { U254_29::OP_PUSH_U32LESLICE(&shifted.to_u32_digits()) }
                { U254_29::OP_EQUALVERIFY(1,0) }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_shl4_overflowing_29() {
        let script = script! {
            { 0b11111110110001111111101110110 }
            { 0b11011010100010001100000101110 }
            { shl4_overflowing_29(2, true) }
            { 0b10101000100011000001011100000 } OP_EQUALVERIFY
            { 0b11101100011111111011101101101 } OP_EQUALVERIFY
            { 0b1111 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);

        let script = script! {
            {     0b1100101011010011011101110 }
            { 0b01101010000100111001001000101 }
            { shl4_overflowing_29(2, false) }
            { 0b10100001001110010010001010000 } OP_EQUALVERIFY
            { 0b11001010110100110111011100110 } OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
