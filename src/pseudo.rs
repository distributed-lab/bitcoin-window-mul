#![allow(non_snake_case)]
#![allow(dead_code)]

use crate::treepp::{pushable, script, Script};

pub fn OP_CHECKSEQUENCEVERIFY() -> Script {
    script! {OP_CSV}
}

/// OP_4PICK
/// The 4 items n back in the stack are copied to the top.
pub fn OP_4PICK() -> Script {
    script! {
        OP_ADD
        OP_DUP  OP_PICK OP_SWAP
        OP_DUP  OP_PICK OP_SWAP
        OP_DUP  OP_PICK OP_SWAP
        OP_1SUB OP_PICK
    }
}

/// OP_BITAND
/// The top two items are bitwise ANDed
pub fn OP_BITAND() -> Script {
    // a and b = 1 iff a + b = 2
    script! {
        OP_ADD 2 OP_EQUAL
    }
}

/// OP_4BITMUL
///
/// Taken from https://github.com/coins/bitcoin-scripts/blob/master/op_mul.md
pub fn OP_4BITMUL() -> Script {
    script! {
        0
        OP_TOALTSTACK

        OP_DUP
        8
        OP_GREATERTHANOREQUAL
        OP_IF
            8
            OP_SUB
            OP_SWAP
            OP_DUP
            OP_DUP OP_ADD OP_DUP OP_ADD OP_DUP OP_ADD
            OP_FROMALTSTACK
            OP_ADD
            OP_TOALTSTACK
            OP_SWAP
        OP_ENDIF

        OP_DUP
        4
        OP_GREATERTHANOREQUAL
        OP_IF
            4
            OP_SUB
            OP_SWAP
            OP_DUP
            OP_DUP OP_ADD OP_DUP OP_ADD
            OP_FROMALTSTACK
            OP_ADD
            OP_TOALTSTACK
            OP_SWAP
        OP_ENDIF

        OP_DUP
        2
        OP_GREATERTHANOREQUAL
        OP_IF
            2
            OP_SUB
            OP_SWAP
            OP_DUP
            OP_DUP OP_ADD
            OP_FROMALTSTACK
            OP_ADD
            OP_TOALTSTACK
            OP_SWAP
        OP_ENDIF

        OP_NOT
        OP_IF
            OP_DROP
            0
        OP_ENDIF

        OP_FROMALTSTACK
        OP_ADD
    }
}

/// OP_4ROLL
/// The 4 items n back in the stack are moved to the top.
pub fn OP_4ROLL() -> Script {
    script! {
        4 OP_ADD
        OP_DUP  OP_ROLL OP_SWAP
        OP_DUP  OP_ROLL OP_SWAP
        OP_DUP  OP_ROLL OP_SWAP
        OP_1SUB OP_ROLL
    }
}

/// Duplicates the top 4 items
pub fn OP_4DUP() -> Script {
    script! {
        OP_2OVER OP_2OVER
    }
}

/// Drops the top 3 items
pub fn OP_3DROP() -> Script {
    script! {
        OP_2DROP OP_DROP
    }
}

/// Drops the top 4 items
pub fn OP_4DROP() -> Script {
    script! {
        OP_2DROP OP_2DROP
    }
}

/// Swaps the top two groups of 4 items
pub fn OP_4SWAP() -> Script {
    script! {
        7 OP_ROLL 7 OP_ROLL
        7 OP_ROLL 7 OP_ROLL
    }
}

/// Puts the top 4 items onto the top of the alt stack. Removes them from the main stack.
pub fn OP_4TOALTSTACK() -> Script {
    script! {
        OP_TOALTSTACK OP_TOALTSTACK OP_TOALTSTACK OP_TOALTSTACK
    }
}

/// Puts the top 4 items from the altstack onto the top of the main stack. Removes them from the alt stack.
pub fn OP_4FROMALTSTACK() -> Script {
    script! {
        OP_FROMALTSTACK OP_FROMALTSTACK OP_FROMALTSTACK OP_FROMALTSTACK
    }
}

//
// Multiplication by Powers of 2
//

/// The top stack item is multiplied by 2
pub fn OP_2MUL() -> Script {
    script! {
        OP_DUP OP_ADD
    }
}

/// The top stack item is multiplied by 4
pub fn OP_4MUL() -> Script {
    script! {
        OP_DUP OP_ADD OP_DUP OP_ADD
    }
}

/// The top stack item is multiplied by 2**k
pub fn op_2k_mul(k: u32) -> Script {
    script! {
        for _ in 0..k{
            {OP_2MUL()}
        }
    }
}

/// The top stack item is multiplied by 16
pub fn OP_16MUL() -> Script {
    script! {
        OP_DUP OP_ADD OP_DUP OP_ADD
        OP_DUP OP_ADD OP_DUP OP_ADD
    }
}

/// The top stack item is multiplied by 256
pub fn OP_256MUL() -> Script {
    script! {
        OP_DUP OP_ADD OP_DUP OP_ADD
        OP_DUP OP_ADD OP_DUP OP_ADD
        OP_DUP OP_ADD OP_DUP OP_ADD
        OP_DUP OP_ADD OP_DUP OP_ADD
    }
}

/// Duplicates the top item `n` times
pub fn OP_NDUP(n: usize) -> Script {
    let times_3_dup = if n > 3 { (n - 3) / 3 } else { 0 };
    let remaining = if n > 3 { (n - 3) % 3 } else { 0 };

    script! {
        if n >= 1 {
            OP_DUP
        }
        if n >= 3 {
            OP_2DUP
        }
        else if n >= 2{
            OP_DUP
        }

        for _ in 0..times_3_dup {
            OP_3DUP
        }

        if remaining == 2{
            OP_2DUP
        }
        else if remaining == 1{
            OP_DUP
        }
    }
}

/// Pushes the same element `n` times.
pub fn OP_CLONE(element: usize, n: usize) -> Script {
    script! {
        if n >= 1 {
            {element} {OP_NDUP(n - 1)}
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{pseudo::OP_4BITMUL, treepp::*};
    use bitcoin_script::script;

    use crate::execute_script;

    use super::OP_BITAND;

    #[test]
    fn test_op_bitand() {
        let script = script! {
            1 1 OP_BITAND 1 OP_EQUALVERIFY
            1 0 OP_BITAND 0 OP_EQUALVERIFY
            0 1 OP_BITAND 0 OP_EQUALVERIFY
            0 0 OP_BITAND 0 OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "trivial case (1,1) failed");
    }

    #[test]
    fn test_op_4bitmul() {
        const TESTS_NUM: usize = 10;

        for _ in 0..TESTS_NUM {
            let a = rand::random::<u8>() as u32;
            let mut b = rand::random::<u8>() as u32;
            b = b % (1 << 4);

            let script = script! {
                {a}
                {b}
                OP_4BITMUL
                {a * b}
                OP_EQUALVERIFY
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success, "trivial case ({}, {}) failed", a, b);
        }
    }
}
