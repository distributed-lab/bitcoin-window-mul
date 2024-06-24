use crate::bigint::bits::limb_to_be_bits_toaltstack;
use crate::bigint::BigInt;
use crate::pseudo::{OP_3DROP, OP_BITAND};
use crate::treepp::*;

impl<const N_BITS: usize, const LIMB_SIZE: usize> BigInt<N_BITS, LIMB_SIZE> {
    /// Takes the top stack big integer and outputs
    /// the naf representation in the main stack
    pub fn convert_to_be_naf_bits() -> Script {
        script! {
            { Self::convert_to_be_bits_toaltstack() }
            { binary_to_be_naf(Self::N_BITS) }
        }
    }
    
    /// Takes the top stack big integer and outputs
    /// the naf representation in the alt stack
    pub fn convert_to_be_naf_bits_toaltstack() -> Script {
        script! {
            { Self::convert_to_be_bits_toaltstack() }
            { binary_to_be_naf(Self::N_BITS) }

            // Moving everything to the alt stack
            // NOTE: The naf representation is one bit longer than the binary one
            for _ in 0..Self::N_BITS + 1 {
                OP_TOALTSTACK
            }
        }
    }

    /// Takes the top stack big integer and outputs
    /// the w-width form in the alt stack
    pub fn convert_to_w_width_form_altstack<const WIDTH: usize>() -> Script {
        script! {
            { Self::convert_to_be_bits_toaltstack() }
            { binary_to_w_width_form_altstack::<WIDTH>(Self::N_BITS) }
        }
    }
}

/// Given bit and carry, conducts the following:
///
/// 1. If carry is `0`, does noting.
/// 2. If carry is `1`, if the bit is `0`, sets the bit to `1` and carry to `0`.
/// 3. If carry is `1`, if the bit is `1`, sets the bit to `0` and does not modify carry.
fn bit_add_carry() -> Script {
    // TODO: This can be probably optimized
    script! {
        OP_DUP
        OP_IF
            // Checking the last bit
            OP_SWAP
            OP_DUP
            OP_IF
                // In case the last bit is 1, we set it to 0 and do not change carry
                OP_DROP 0 OP_SWAP
            OP_ELSE
                // In case the last bit is 0, we set it to 1 and change carry to 0
                OP_DROP 1
                OP_SWAP
                OP_DROP 0
            OP_ENDIF
        OP_ENDIF
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// NAF representation with a size `num_bits+1`. 
/// It pushes all the bits to the alt stack except for the most significant bit. 
/// The first element in the alt stack (except for one left in the main stack) 
/// is the least significant limb.
pub fn binary_to_be_naf(num_bits: usize) -> Script {
    script! {
        // We also have top two stack elements + carry in the front
        OP_FROMALTSTACK
        0 // Carry initialization

        for _ in 0..num_bits - 1 {
            OP_FROMALTSTACK
            OP_SWAP
            // At this point, we have two bits and carry at the front

            bit_add_carry // Add the last bit and carry

            // Now we have the last bit in the stack and carry in the front
            // Checking whether we get the pattern {1,1} and in case we do, we need to change it to {-1,0},
            // and change the carry accordingly (to 1)

            // From (bit1, bit2, carry) to (carry, bit1, bit2)
            OP_ROT OP_ROT

            // Checking whether bit1 = bit2 = 1
            OP_2DUP OP_BITAND OP_IF
                // In case they are both 1, we need to change them to -1 and 0, while the carry must be one
                OP_3DROP
                1 -1 0
            OP_ENDIF

            OP_ROT
        }
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// 3-width representation. 
pub fn binary_to_w_width_form<const WIDTH: usize>(num_bits: usize) -> Script {
    // The number of coefficients in the w-width form
    let decomposition_size = (num_bits + WIDTH - 1) / WIDTH;
    let head_size = num_bits - (decomposition_size - 1) * WIDTH;

    script! {
        for i in 0..decomposition_size {
            if i + 1 == decomposition_size {
                // Picking the remaining bits in head and calculating 1<<j
                for j in 0..head_size {
                    OP_FROMALTSTACK
                    OP_IF { 1 << j } OP_ELSE { 0 } OP_ENDIF
                }
                // Adding the coefficients (we need head_size-1 add ops)
                for _ in 0..head_size-1 { OP_ADD }
            } else {
                // Picking top w bits from the stack and calculating 1<<j
                for j in 0..WIDTH {
                    OP_FROMALTSTACK
                    OP_IF { 1 << j } OP_ELSE { 0 } OP_ENDIF
                }
                // Adding the coefficients (we need WIDTH-1 add ops)
                for _ in 0..WIDTH-1 { OP_ADD }
            }
        }
    }
}

/// Converts the limb from the top stack which has `num_bits` bits in size to
/// 3-width representation. It pushes all the coefficients to the alt stack
pub fn binary_to_w_width_form_altstack<const WIDTH: usize>(num_bits: usize) -> Script {
    // The number of coefficients in the w-width form
    let decomposition_size = (num_bits + WIDTH - 1) / WIDTH;

    script!{
        { binary_to_w_width_form::<WIDTH>(num_bits) }

        // Moving the result to the alt stack
        for _ in 0..decomposition_size {
            OP_TOALTSTACK
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::bits::limb_to_be_bits_toaltstack;
    use crate::bigint::naf::{binary_to_be_naf, binary_to_w_width_form_altstack};
    use crate::bigint::U254;
    use crate::{print_script_size, treepp::*};
    use ark_ff::{One, Zero};
    use num_bigint::{BigInt, BigUint, RandomBits, ToBigInt, ToBigUint};
    use num_traits::FromPrimitive;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    /// Tests the binary-to-naf conversion for a trivial case.
    #[test]
    fn test_limb_to_naf_trivial() {
        // Launching a script for {0, 1} in binary
        let script = script! {
            { 2 } // {0, 1} in binary
            { limb_to_be_bits_toaltstack(2) }
            { binary_to_be_naf(2) }
            0 OP_EQUALVERIFY
            1 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "trivial case (0, 1) failed");

        // Launching a script for {1, 1} in binary
        let script = script! {
            { 3 } // {1, 1} in binary
            { limb_to_be_bits_toaltstack(2) }
            { binary_to_be_naf(2) }
            1 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            -1 OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "trivial case (1, 1) failed");

        // Launching a script for {1, 1, 1} in binary
        let script = script! {
            { 7 } // {1, 1, 1} in binary
            { limb_to_be_bits_toaltstack(3) }
            { binary_to_be_naf(3) }
            // Should get {-1, 0, 0, 1}
            1 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            -1 OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "trivial case (1, 1, 1) failed");

        // Launching a script for {0, 1, 1, 1} in binary
        let script = script! {
            { 14 } // {0, 1, 1, 1} in binary
            { limb_to_be_bits_toaltstack(5) }
            { binary_to_be_naf(4) }
            // Should get {0, -1, 0, 0, 1}
            1 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            -1 OP_EQUALVERIFY
            0 OP_EQUALVERIFY
            OP_TRUE
        };

        let exec_result = execute_script(script);
        assert!(exec_result.success, "trivial case (0, 1, 1, 1) failed");
    }

    /// Tests the binary-to-naf conversion for random case
    #[test]
    fn test_limb_to_naf() {
        /// Number of bits for the single limb
        const BITS_NUM: usize = 30;
        /// Number of tests to generate
        const TESTS_NUM: usize = 100;

        print_script_size("binary_to_naf", binary_to_be_naf(BITS_NUM));

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            // Picking a random number
            let test_number: u32 = prng.gen_range(0..1 << BITS_NUM as u32);

            // Decomposing a number into wnaf representation
            let mut wnaf_decomposition = {
                let mut decomposition = vec![];
                let mut k = test_number.clone();

                while k >= 1 {
                    if k % 2 == 1 {
                        let c: i32 = 2 - (k % 4) as i32;
                        decomposition.push(c);
                        k = (k as i32 - c) as u32;
                    } else {
                        decomposition.push(0i32);
                    }

                    k = k / 2;
                }

                decomposition
            };

            wnaf_decomposition.resize(BITS_NUM + 1, 0);
            assert_eq!(
                wnaf_decomposition.len(),
                BITS_NUM + 1,
                "wnaf decomposition has incorrect length"
            );

            // Verifying that the decomposition was done correctly
            let from_wnaf_value = wnaf_decomposition
                .iter()
                .enumerate()
                .fold(0, |acc, (i, c)| acc + c * 2i32.pow(i as u32));
            assert_eq!(
                test_number as i32, from_wnaf_value,
                "wnaf decomposition was done incorrectly"
            );

            // Launching a script
            let script = script! {
                { test_number }
                { limb_to_be_bits_toaltstack(BITS_NUM) }
                { binary_to_be_naf(BITS_NUM) }
                for coefficient in wnaf_decomposition.iter().rev() {
                    { *coefficient }
                    OP_EQUALVERIFY
                }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    /// Tests the conversion of a big integer to wnaf representation
    #[test]
    fn test_bigint_to_naf() {
        const TESTS_NUM: usize = 10;

        print_script_size("u254_to_wnaf", U254::convert_to_be_naf_bits());

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            let test_number: BigUint = prng.sample(RandomBits::new(254));

            // Decomposing a number into wnaf representation
            let mut wnaf_decomposition = {
                let mut decomposition = vec![];
                let mut k = test_number.to_bigint().unwrap();

                while k.ge(&BigInt::one()) {
                    let modulo_2: BigInt = k.clone() % 2;

                    let modulo_4: BigInt = k.clone() % 4;
                    let (_, modulo_4) = modulo_4.to_u32_digits();
                    let modulo_4 = {
                        if modulo_4.len() == 0 {
                            0
                        } else {
                            modulo_4[0]
                        }
                    };

                    if modulo_2.eq(&BigInt::one()) {
                        let c: i32 = 2 - modulo_4 as i32;
                        decomposition.push(c);
                        k = k.checked_sub(&BigInt::from_i32(c).unwrap()).unwrap();
                    } else {
                        decomposition.push(0i32);
                    }

                    k = k / 2;
                }

                decomposition
            };

            // Verifying that the decomposition was done correctly
            let from_wnaf_value =
                wnaf_decomposition
                    .iter()
                    .enumerate()
                    .fold(BigInt::zero(), |acc, (i, c)| {
                        let addition = c.to_bigint().unwrap()
                            * BigInt::pow(&2.to_bigint().unwrap(), i as u32);
                        acc + addition
                    });
            assert_eq!(
                test_number, from_wnaf_value.to_biguint().unwrap(),
                "wnaf decomposition was done incorrectly"
            );

            wnaf_decomposition.resize(255, 0);
            assert_eq!(wnaf_decomposition.len(), 255, "wnaf decomposition has incorrect length");

            // Launching a script
            let script = script! {
                { U254::push_u32_le(&test_number.to_u32_digits()) }
                { U254::convert_to_be_naf_bits() }
                for coefficient in wnaf_decomposition.iter().rev() {
                    { *coefficient }
                    OP_EQUALVERIFY
                }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    /// Tests the conversion of a big integer to wnaf representation and 
    /// additionally pushed to the alt stack.
    #[test]
    fn test_bigint_to_naf_altstack() {
        const TESTS_NUM: usize = 10;

        print_script_size("u254_to_wnaf_altstack", U254::convert_to_be_naf_bits_toaltstack());

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            let test_number: BigUint = prng.sample(RandomBits::new(254));

            // Decomposing a number into wnaf representation
            let mut wnaf_decomposition = {
                let mut decomposition = vec![];
                let mut k = test_number.to_bigint().unwrap();

                while k.ge(&BigInt::one()) {
                    let modulo_2: BigInt = k.clone() % 2;

                    let modulo_4: BigInt = k.clone() % 4;
                    let (_, modulo_4) = modulo_4.to_u32_digits();
                    let modulo_4 = {
                        if modulo_4.len() == 0 {
                            0
                        } else {
                            modulo_4[0]
                        }
                    };

                    if modulo_2.eq(&BigInt::one()) {
                        let c: i32 = 2 - modulo_4 as i32;
                        decomposition.push(c);
                        k = k.checked_sub(&BigInt::from_i32(c).unwrap()).unwrap();
                    } else {
                        decomposition.push(0i32);
                    }

                    k = k / 2;
                }

                decomposition
            };

            // Verifying that the decomposition was done correctly
            let from_wnaf_value =
                wnaf_decomposition
                    .iter()
                    .enumerate()
                    .fold(BigInt::zero(), |acc, (i, c)| {
                        let addition = c.to_bigint().unwrap()
                            * BigInt::pow(&2.to_bigint().unwrap(), i as u32);
                        acc + addition
                    });
            assert_eq!(
                test_number, from_wnaf_value.to_biguint().unwrap(),
                "wnaf decomposition was done incorrectly"
            );

            wnaf_decomposition.resize(255, 0);
            assert_eq!(wnaf_decomposition.len(), 255, "wnaf decomposition has incorrect length");

            // Launching a script
            let script = script! {
                { U254::push_u32_le(&test_number.to_u32_digits()) }
                { U254::convert_to_be_naf_bits_toaltstack() }
                for coefficient in wnaf_decomposition {
                    OP_FROMALTSTACK
                    { coefficient }
                    OP_EQUALVERIFY
                }
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }

    #[test]
    fn test_30bit_limb_to_3_width_form() {
        /// The number of tests to conduct
        const LIMB_BIT_SIZE: usize = 30;
        const WINDOW_WIDTH: usize = 3;
        const TESTS_NUM: usize = 30;

        for _ in 0..TESTS_NUM {
            // Picking a random 30-bit number
            let limb: u32 = rand::random::<u32>() % (1 << LIMB_BIT_SIZE);

            // Decomposing into the 3-width form
            let mut decomposition = vec![];
            let mut k = limb.clone();

            while k >= 1 {
                let c = k % (1 << WINDOW_WIDTH);
                decomposition.push(c);
                k = k - c;
                k = k / (1 << WINDOW_WIDTH);
            }

            // Asserting that decomposition is indeed correct
            let from_decomposition = decomposition.iter().enumerate().fold(0, |acc, (i, c)| {
                acc + c * (1 << (WINDOW_WIDTH*i))
            });
            assert_eq!(limb, from_decomposition, "decomposition was done incorrectly");

            let script = script! {
                { limb } // 30-bit number
                { limb_to_be_bits_toaltstack(LIMB_BIT_SIZE) }
                { binary_to_w_width_form_altstack::<WINDOW_WIDTH>(LIMB_BIT_SIZE) }

                for coefficient in decomposition {
                    OP_FROMALTSTACK
                    { coefficient }
                    OP_EQUALVERIFY
                }

                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success, "30-bit limb to 3-width form failed");
        }
    }

    #[test]
    fn test_23bit_limb_to_4_width_form() {
        /// The number of tests to conduct
        const LIMB_BIT_SIZE: usize = 23;
        const WINDOW_WIDTH: usize = 4;
        const TESTS_NUM: usize = 30;

        for _ in 0..TESTS_NUM {
            // Picking a random 30-bit number
            let limb: u32 = rand::random::<u32>() % (1 << LIMB_BIT_SIZE);

            // Decomposing into the 3-width form
            let mut decomposition = vec![];
            let mut k = limb.clone();

            while k >= 1 {
                let c = k % (1 << WINDOW_WIDTH);
                decomposition.push(c);
                k = k - c;
                k = k / (1 << WINDOW_WIDTH);
            }

            // Asserting that decomposition is indeed correct
            let from_decomposition = decomposition.iter().enumerate().fold(0, |acc, (i, c)| {
                acc + c * (1 << (WINDOW_WIDTH*i))
            });
            assert_eq!(limb, from_decomposition, "decomposition was done incorrectly");

            let script = script! {
                { limb } // 30-bit number
                { limb_to_be_bits_toaltstack(LIMB_BIT_SIZE) }
                { binary_to_w_width_form_altstack::<WINDOW_WIDTH>(LIMB_BIT_SIZE) }

                for coefficient in decomposition {
                    OP_FROMALTSTACK
                    { coefficient }
                    OP_EQUALVERIFY
                }

                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success, "30-bit limb to 3-width form failed");
        }
    }

    #[test]
    fn test_254_bit_to_w_width() {
        /// The number of tests to conduct
        const TESTS_NUM: usize = 30;
        const WINDOW_WIDTH: usize = 3;

        print_script_size("u254_to_3_width_form", U254::convert_to_w_width_form_altstack::<WINDOW_WIDTH>());

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            let test_number: BigUint = prng.sample(RandomBits::new(254));

            // Decomposing a number into wnaf representation
            let mut decomposition = {
                let mut decomposition = vec![];
                let mut k = test_number.clone();
                let window_size = (1 << WINDOW_WIDTH).to_biguint().unwrap();

                while k.ge(&BigUint::one()) {
                    // TODO: I do not know what I am doing with so many clones, so FIXME later please
                    let c: BigUint = k.clone() % window_size.clone();
                    decomposition.push(c.clone());
                    k = k - c;
                    k = k / window_size.clone();
                }

                decomposition
            };

            // Verifying that the decomposition was done correctly
            let from_decomposition = decomposition.iter().enumerate().fold(BigInt::zero(), |acc, (i, c)| {
                let power_of_two = BigInt::from_u8(2u8).unwrap().pow((WINDOW_WIDTH*i) as u32);
                acc + c.to_bigint().unwrap() * power_of_two
            });
            assert_eq!(test_number, from_decomposition.to_biguint().unwrap(), "w-width decomposition was done incorrectly");

            decomposition.resize(254/WINDOW_WIDTH + 1, 0.to_biguint().unwrap());
            assert_eq!(decomposition.len(), 254/WINDOW_WIDTH + 1, "w-width decomposition has incorrect length");

            // Converting to u32 array
            let decomposition = decomposition.iter().map(|c| {
                let digits = c.to_u32_digits();
                assert!(digits.len() <= 1, "big integer has more than one digit");
                if digits.len() == 0 {
                    0
                } else {
                    digits[0]
                }
            }).collect::<Vec<_>>();

            // Launching a script
            let script = script! {
                { U254::push_u32_le(&test_number.to_u32_digits()) }
                { U254::convert_to_w_width_form_altstack::<WINDOW_WIDTH>() }
                for coefficient in decomposition {
                    OP_FROMALTSTACK
                    { coefficient }
                    OP_EQUALVERIFY
                }
                
                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success);
        }
    }
}
