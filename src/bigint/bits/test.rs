use crate::bigint::bits::implementation::{limb_to_be_bits, limb_to_le_bits};
use crate::bigint::{U254, U64};
use crate::traits::bitable::Bitable;
use crate::traits::integer::{NonNativeInteger, NonNativeLimbInteger};
use crate::treepp::{execute_script, pushable};
use bitcoin_script::script;
use core::ops::ShrAssign;
use num_bigint::{BigUint, RandomBits};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

#[test]
fn test_limb_to_be_bits() {
    println!(
        "limb_to_be_bits(30): takes {:?} bytes",
        script! { {limb_to_be_bits(30)} }.len()
    );
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..100 {
        let mut a: u32 = prng.gen();
        a %= 1 << 30;

        let mut bits = vec![];
        let mut cur = a;
        for _ in 0..30 {
            bits.push(cur % 2);
            cur /= 2;
        }

        let script = script! {
            { a }
            { limb_to_be_bits(30) }
            for bit in bits.iter().rev() {
                { *bit }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let mut a: u32 = prng.gen();
        a %= 1 << 15;

        println!("a = {:?}", a);

        let mut bits = vec![];
        let mut cur = a;
        for _ in 0..15 {
            bits.push(cur % 2);
            cur /= 2;
        }

        println!("bits = {:?}", bits);

        let script = script! {
            { a }
            { limb_to_be_bits(15) }
            for bit in bits.iter().rev() {
                { *bit }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for a in 0..4 {
        let script = script! {
            { a }
            { limb_to_be_bits(2) }
            { a >> 1 } OP_EQUALVERIFY
            { a & 1 } OP_EQUAL
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for a in 0..2 {
        let script = script! {
            { a }
            { limb_to_be_bits(1) }
            { a } OP_EQUAL
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    let script = script! {
        0 { limb_to_be_bits(0) } 0 OP_EQUAL
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success);
}

#[test]
fn test_limb_to_le_bits() {
    println!(
        "limb_to_le_bits(30): {:?} bytes",
        script! { {limb_to_be_bits(30)} }.len()
    );
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..100 {
        let mut a: u32 = prng.gen();
        a %= 1 << 30;

        let mut bits = vec![];
        let mut cur = a;
        for _ in 0..30 {
            bits.push(cur % 2);
            cur /= 2;
        }

        let script = script! {
            { a }
            { limb_to_le_bits(30) }
            for i in 0..30 {
                { bits[i] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..100 {
        let mut a: u32 = prng.gen();
        a %= 1 << 15;

        let mut bits = vec![];
        let mut cur = a;
        for _ in 0..15 {
            bits.push(cur % 2);
            cur /= 2;
        }

        let script = script! {
            { a }
            { limb_to_le_bits(15) }
            for i in 0..15 {
                { bits[i] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for a in 0..4 {
        let script = script! {
            { a }
            { limb_to_le_bits(2) }
            { a & 1 } OP_EQUALVERIFY
            { a >> 1 } OP_EQUAL
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for a in 0..2 {
        let script = script! {
            { a }
            { limb_to_le_bits(1) }
            { a } OP_EQUAL
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    let script = script! {
        0 { limb_to_le_bits(0) } 0 OP_EQUAL
    };

    let exec_result = execute_script(script);
    assert!(exec_result.success);
}

#[test]
fn test_ubigint_to_be_bits() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U254::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U254::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_TOBEBITS() }
            for i in 0..U254::N_BITS {
                { bits[(U254::N_BITS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U64::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U64::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_TOBEBITS() }
            for i in 0..U64::N_BITS {
                { bits[(U64::N_BITS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_ubigint_to_le_bits() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U254::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U254::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_TOLEBITS() }
            for i in 0..U254::N_BITS {
                { bits[i as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U64::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U64::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_TOLEBITS() }
            for i in 0..U64::N_BITS {
                { bits[i as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_ubigint_to_be_bits_toaltstack() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U254::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U254::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_TOBEBITS_TOALTSTACK() }
            for i in 0..U254::N_BITS {
                OP_FROMALTSTACK
                { bits[i as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U64::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U64::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_TOBEBITS_TOALTSTACK() }
            for i in 0..U64::N_BITS {
                OP_FROMALTSTACK
                { bits[i as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}

#[test]
fn test_ubigint_to_le_bits_toaltstack() {
    let mut prng = ChaCha20Rng::seed_from_u64(0);

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U254::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U254::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U254::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U254::OP_TOLEBITS_TOALTSTACK() }
            for i in 0..U254::N_BITS {
                OP_FROMALTSTACK
                { bits[(U254::N_BITS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }

    for _ in 0..10 {
        let a: BigUint = prng.sample(RandomBits::new(U64::N_BITS as u64));

        let mut bits = vec![];
        let mut cur = a.clone();
        for _ in 0..U64::N_BITS {
            bits.push(if cur.bit(0) { 1 } else { 0 });
            cur.shr_assign(1);
        }

        let script = script! {
            { U64::OP_PUSH_U32LESLICE(&a.to_u32_digits()) }
            { U64::OP_TOLEBITS_TOALTSTACK() }
            for i in 0..U64::N_BITS {
                OP_FROMALTSTACK
                { bits[(U64::N_BITS - 1 - i) as usize] }
                OP_EQUALVERIFY
            }
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success);
    }
}
