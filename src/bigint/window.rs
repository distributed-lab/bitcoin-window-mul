use crate::treepp::*;

use super::NonNativeBigInt;

impl<const N_BITS: usize, const LIMB_SIZE: usize> NonNativeBigInt<N_BITS, LIMB_SIZE> {
    /// Takes the top stack big integer and outputs
    /// the low-endian w-width form in the alt stack
    #[allow(dead_code)]
    pub(super) fn convert_to_le_w_width_form_toaltstack<const WIDTH: usize>() -> Script {
        script! {
            { Self::convert_to_be_bits_toaltstack() }
            { binary_to_w_width_form_altstack::<WIDTH>(Self::N_BITS) }
        }
    }

    /// Takes the top stack big integer and outputs
    /// the big-endian w-width form in the alt stack
    pub(super) fn convert_to_be_w_width_form_toaltstack<const WIDTH: usize>() -> Script {
        let decomposition_size = (Self::N_BITS + WIDTH - 1) / WIDTH;

        script! {
            { Self::convert_to_be_bits_toaltstack() }
            { binary_to_w_width_form::<WIDTH>(Self::N_BITS) }

            // Moving the result to the alt stack in the reverse order
            for i in (0..decomposition_size).rev() {
                {i} OP_ROLL
                OP_TOALTSTACK
            }
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

    script! {
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
    use crate::bigint::window::binary_to_w_width_form_altstack;
    use crate::bigint::U254;
    use crate::traits::integer::NonNativeInteger;
    use crate::{print_script_size, treepp::*};
    use ark_ff::{One, Zero};
    use num_bigint::{BigInt as NumBigInt, BigUint as NumBigUInt, RandomBits, ToBigInt, ToBigUint};
    use num_traits::FromPrimitive;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

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
            let from_decomposition = decomposition
                .iter()
                .enumerate()
                .fold(0, |acc, (i, c)| acc + c * (1 << (WINDOW_WIDTH * i)));
            assert_eq!(
                limb, from_decomposition,
                "decomposition was done incorrectly"
            );

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
            let from_decomposition = decomposition
                .iter()
                .enumerate()
                .fold(0, |acc, (i, c)| acc + c * (1 << (WINDOW_WIDTH * i)));
            assert_eq!(
                limb, from_decomposition,
                "decomposition was done incorrectly"
            );

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

        print_script_size(
            "u254_to_3_width_form",
            U254::convert_to_le_w_width_form_toaltstack::<WINDOW_WIDTH>(),
        );

        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..TESTS_NUM {
            let test_number: NumBigUInt = prng.sample(RandomBits::new(254));

            // Decomposing a number into wnaf representation
            let mut decomposition = {
                let mut decomposition = vec![];
                let mut k = test_number.clone();
                let window_size = (1 << WINDOW_WIDTH).to_biguint().unwrap();

                while k.ge(&NumBigUInt::one()) {
                    // TODO: I do not know what I am doing with so many clones, so FIXME later please
                    let c: NumBigUInt = k.clone() % window_size.clone();
                    decomposition.push(c.clone());
                    k = k - c;
                    k = k / window_size.clone();
                }

                decomposition
            };

            // Verifying that the decomposition was done correctly
            let from_decomposition =
                decomposition
                    .iter()
                    .enumerate()
                    .fold(NumBigInt::zero(), |acc, (i, c)| {
                        let power_of_two = NumBigInt::from_u8(2u8)
                            .unwrap()
                            .pow((WINDOW_WIDTH * i) as u32);
                        acc + c.to_bigint().unwrap() * power_of_two
                    });
            assert_eq!(
                test_number,
                from_decomposition.to_biguint().unwrap(),
                "w-width decomposition was done incorrectly"
            );

            decomposition.resize(254 / WINDOW_WIDTH + 1, 0.to_biguint().unwrap());
            assert_eq!(
                decomposition.len(),
                254 / WINDOW_WIDTH + 1,
                "w-width decomposition has incorrect length"
            );

            // Converting to u32 array
            let decomposition = decomposition
                .iter()
                .map(|c| {
                    let digits = c.to_u32_digits();
                    assert!(digits.len() <= 1, "big integer has more than one digit");
                    if digits.len() == 0 {
                        0
                    } else {
                        digits[0]
                    }
                })
                .collect::<Vec<_>>();

            // Launching a script in le order
            let script = script! {
                { U254::OP_PUSHU32LESLICE(&test_number.to_u32_digits()) }
                { U254::convert_to_le_w_width_form_toaltstack::<WINDOW_WIDTH>() }
                for coefficient in decomposition.iter() {
                    OP_FROMALTSTACK
                    { *coefficient }
                    OP_EQUALVERIFY
                }

                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success, "le w-width form failed");

            // Launching a script in be order
            let script = script! {
                { U254::OP_PUSHU32LESLICE(&test_number.to_u32_digits()) }
                { U254::convert_to_be_w_width_form_toaltstack::<WINDOW_WIDTH>() }
                for coefficient in decomposition.iter().rev() {
                    OP_FROMALTSTACK
                    { *coefficient }
                    OP_EQUALVERIFY
                }

                OP_TRUE
            };

            let exec_result = execute_script(script);
            assert!(exec_result.success, "be w-width form failed");
        }
    }
}
