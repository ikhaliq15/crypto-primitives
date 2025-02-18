use std::borrow::Borrow;
use std::marker::PhantomData;
use ark_ff::{PrimeField};
use ark_r1cs_std::{R1CSVar};
use ark_r1cs_std::alloc::{AllocationMode, AllocVar};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::uint8::UInt8;
use ark_relations::r1cs::{Namespace, SynthesisError};
use crate::encryption::aes::{Aes128, Ciphertext, Key, Parameters, Plaintext, Randomness};
use crate::encryption::SymmetricEncryptionGadget;

pub type AesState<ConstraintF> = [UInt64<ConstraintF>; 8];
pub type AesRoundKey<ConstraintF> = [UInt64<ConstraintF>; 8]; // TODO: use this?

#[allow(dead_code)]
pub struct Aes128Gadget<ConstraintF: PrimeField> {
    t: UInt8<ConstraintF>
}

// Round constants helper table for AES-128.
// Source: FIPS-197, https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf
const RCON: [u8; 10] = [ 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36 ];

// SBOX helper table for AES.
// Source: https://github.com/yahu/AES/blob/master/SBOX.txt
const SBOX: [u8; 256] =
    [
        0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30, 0x1,0x67,0x2b,0xfe,0xd7,0xab,0x76,
        0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
        0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
        0x4,0xc7,0x23,0xc3,0x18,0x96, 0x5,0x9a, 0x7,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
        0x9,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
        0x53,0xd1,   0,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
        0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9, 0x2,0x7f,0x50,0x3c,0x9f,0xa8,
        0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
        0xcd, 0xc,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
        0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e, 0xb,0xdb,
        0xe0,0x32,0x3a, 0xa,0x49, 0x6,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
        0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae, 0x8,
        0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
        0x70,0x3e,0xb5,0x66,0x48, 0x3,0xf6, 0xe,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
        0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
        0x8c,0xa1,0x89, 0xd,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d, 0xf,0xb0,0x54,0xbb,0x16,
    ];

// Multiplication look-up tables.
// Source: https://github.com/devershichandra27/C-implementation-of-AES/blob/master/AES.c
const MUL2: [u8; 256] = [
    0x00,0x02,0x04,0x06,0x08,0x0a,0x0c,0x0e,0x10,0x12,0x14,0x16,0x18,0x1a,0x1c,0x1e,
    0x20,0x22,0x24,0x26,0x28,0x2a,0x2c,0x2e,0x30,0x32,0x34,0x36,0x38,0x3a,0x3c,0x3e,
    0x40,0x42,0x44,0x46,0x48,0x4a,0x4c,0x4e,0x50,0x52,0x54,0x56,0x58,0x5a,0x5c,0x5e,
    0x60,0x62,0x64,0x66,0x68,0x6a,0x6c,0x6e,0x70,0x72,0x74,0x76,0x78,0x7a,0x7c,0x7e,
    0x80,0x82,0x84,0x86,0x88,0x8a,0x8c,0x8e,0x90,0x92,0x94,0x96,0x98,0x9a,0x9c,0x9e,
    0xa0,0xa2,0xa4,0xa6,0xa8,0xaa,0xac,0xae,0xb0,0xb2,0xb4,0xb6,0xb8,0xba,0xbc,0xbe,
    0xc0,0xc2,0xc4,0xc6,0xc8,0xca,0xcc,0xce,0xd0,0xd2,0xd4,0xd6,0xd8,0xda,0xdc,0xde,
    0xe0,0xe2,0xe4,0xe6,0xe8,0xea,0xec,0xee,0xf0,0xf2,0xf4,0xf6,0xf8,0xfa,0xfc,0xfe,
    0x1b,0x19,0x1f,0x1d,0x13,0x11,0x17,0x15,0x0b,0x09,0x0f,0x0d,0x03,0x01,0x07,0x05,
    0x3b,0x39,0x3f,0x3d,0x33,0x31,0x37,0x35,0x2b,0x29,0x2f,0x2d,0x23,0x21,0x27,0x25,
    0x5b,0x59,0x5f,0x5d,0x53,0x51,0x57,0x55,0x4b,0x49,0x4f,0x4d,0x43,0x41,0x47,0x45,
    0x7b,0x79,0x7f,0x7d,0x73,0x71,0x77,0x75,0x6b,0x69,0x6f,0x6d,0x63,0x61,0x67,0x65,
    0x9b,0x99,0x9f,0x9d,0x93,0x91,0x97,0x95,0x8b,0x89,0x8f,0x8d,0x83,0x81,0x87,0x85,
    0xbb,0xb9,0xbf,0xbd,0xb3,0xb1,0xb7,0xb5,0xab,0xa9,0xaf,0xad,0xa3,0xa1,0xa7,0xa5,
    0xdb,0xd9,0xdf,0xdd,0xd3,0xd1,0xd7,0xd5,0xcb,0xc9,0xcf,0xcd,0xc3,0xc1,0xc7,0xc5,
    0xfb,0xf9,0xff,0xfd,0xf3,0xf1,0xf7,0xf5,0xeb,0xe9,0xef,0xed,0xe3,0xe1,0xe7,0xe5,
];

const MUL3: [u8; 256] = [
    0x00,0x03,0x06,0x05,0x0c,0x0f,0x0a,0x09,0x18,0x1b,0x1e,0x1d,0x14,0x17,0x12,0x11,
    0x30,0x33,0x36,0x35,0x3c,0x3f,0x3a,0x39,0x28,0x2b,0x2e,0x2d,0x24,0x27,0x22,0x21,
    0x60,0x63,0x66,0x65,0x6c,0x6f,0x6a,0x69,0x78,0x7b,0x7e,0x7d,0x74,0x77,0x72,0x71,
    0x50,0x53,0x56,0x55,0x5c,0x5f,0x5a,0x59,0x48,0x4b,0x4e,0x4d,0x44,0x47,0x42,0x41,
    0xc0,0xc3,0xc6,0xc5,0xcc,0xcf,0xca,0xc9,0xd8,0xdb,0xde,0xdd,0xd4,0xd7,0xd2,0xd1,
    0xf0,0xf3,0xf6,0xf5,0xfc,0xff,0xfa,0xf9,0xe8,0xeb,0xee,0xed,0xe4,0xe7,0xe2,0xe1,
    0xa0,0xa3,0xa6,0xa5,0xac,0xaf,0xaa,0xa9,0xb8,0xbb,0xbe,0xbd,0xb4,0xb7,0xb2,0xb1,
    0x90,0x93,0x96,0x95,0x9c,0x9f,0x9a,0x99,0x88,0x8b,0x8e,0x8d,0x84,0x87,0x82,0x81,
    0x9b,0x98,0x9d,0x9e,0x97,0x94,0x91,0x92,0x83,0x80,0x85,0x86,0x8f,0x8c,0x89,0x8a,
    0xab,0xa8,0xad,0xae,0xa7,0xa4,0xa1,0xa2,0xb3,0xb0,0xb5,0xb6,0xbf,0xbc,0xb9,0xba,
    0xfb,0xf8,0xfd,0xfe,0xf7,0xf4,0xf1,0xf2,0xe3,0xe0,0xe5,0xe6,0xef,0xec,0xe9,0xea,
    0xcb,0xc8,0xcd,0xce,0xc7,0xc4,0xc1,0xc2,0xd3,0xd0,0xd5,0xd6,0xdf,0xdc,0xd9,0xda,
    0x5b,0x58,0x5d,0x5e,0x57,0x54,0x51,0x52,0x43,0x40,0x45,0x46,0x4f,0x4c,0x49,0x4a,
    0x6b,0x68,0x6d,0x6e,0x67,0x64,0x61,0x62,0x73,0x70,0x75,0x76,0x7f,0x7c,0x79,0x7a,
    0x3b,0x38,0x3d,0x3e,0x37,0x34,0x31,0x32,0x23,0x20,0x25,0x26,0x2f,0x2c,0x29,0x2a,
    0x0b,0x08,0x0d,0x0e,0x07,0x04,0x01,0x02,0x13,0x10,0x15,0x16,0x1f,0x1c,0x19,0x1a,
];

// constants for AES-128
// TODO: move these constants somewhere else
const NK: usize = 4;
const NB: usize = 4;
const NR: usize = 10;

impl<ConstraintF: PrimeField> Aes128Gadget<ConstraintF> {

    fn sub_byte(byte: UInt8<ConstraintF>) -> UInt8<ConstraintF> {
        UInt8::constant(SBOX[byte.value().unwrap() as usize])
    }

    // TODO: rename the key_schedule and encrypt functions to something similar to FIPS-197 names.
    // TODO: key scheduler and encrypt have bad rust idioms, i think. probably shouldn't need use .clone so much :\

    // uses Figure 11 in Section 5.2 of https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf
    pub fn aes128_key_schedule(key: [UInt8<ConstraintF>; 16]) -> [[UInt8<ConstraintF>; 4]; NB * (NR + 1)] {
        // helper functions
        // TODO: see if i get rid of these nested functions and move them out of aes128_key_schedule
        fn rcon<ConstraintF: PrimeField>(i: usize) -> [UInt8<ConstraintF>; 4] {
            [
                UInt8::constant(RCON[i-1]),
                UInt8::constant(0u8),
                UInt8::constant(0u8),
                UInt8::constant(0u8),
            ]
        }

        fn xor_words<ConstraintF: PrimeField>(
            a: [UInt8<ConstraintF>; 4],
            b: [UInt8<ConstraintF>; 4]
        ) -> [UInt8<ConstraintF>; 4] {
            [
                a[0].xor(&b[0]).unwrap(),
                a[1].xor(&b[1]).unwrap(),
                a[2].xor(&b[2]).unwrap(),
                a[3].xor(&b[3]).unwrap(),
            ]
        }

        fn rot_word<ConstraintF: PrimeField>(word: [UInt8<ConstraintF>; 4]) -> [UInt8<ConstraintF>; 4] {
            [word[1].clone(), word[2].clone(), word[3].clone(), word[0].clone()]
        }

        fn sub_word<ConstraintF: PrimeField>(word: [UInt8<ConstraintF>; 4]) -> [UInt8<ConstraintF>; 4] {
            word.map(|byte: UInt8<ConstraintF>| Aes128Gadget::sub_byte(byte))
        }

        let mut w: [[UInt8<ConstraintF>; 4]; NB * (NR + 1)] =
            [(); NB * (NR + 1)].map(|_| [
                UInt8::constant(0u8),
                UInt8::constant(0u8),
                UInt8::constant(0u8),
                UInt8::constant(0u8),
            ]);

        let mut i: usize = 0;

        while i < NK {
            w[i] = [key[4*i].clone(), key[4*i+1].clone(), key[4*i+2].clone(), key[4*i+3].clone()];
            i += 1;
        }

        i = NK;

        while i < NB * (NR +1) {
            let mut temp: [UInt8<ConstraintF>; 4] = w[i-1].clone();

            if i % NK == 0 {
                temp = xor_words(sub_word(rot_word(temp)), rcon(i/NK));
            } else if NK > 6 && i % NK == 4 {
                temp = sub_word(temp);
            }

            w[i] = xor_words(w[i-NK].clone(), temp);

            i += 1;
        }

        w
    }

    // uses Figure 5 in Section 5.1 of https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf
    pub fn aes128_encrypt(
        input: [UInt8<ConstraintF>; 4 * NB],
        rkeys: [[UInt8<ConstraintF>; 4]; NB * (NR + 1)]
    ) -> [UInt8<ConstraintF>; 4 * NB] {
        // helper functions
        // TODO: see if i get rid of these nested functions and move them out of aes128_key_schedule
        fn add_round_key<ConstraintF: PrimeField>(
            state: [UInt8<ConstraintF>; 4 * NB],
            rkey: &[[UInt8<ConstraintF>; 4]]
        ) -> [UInt8<ConstraintF>; 4 * NB] {
            assert_eq!(rkey.len(), NB);

            let mut out: [UInt8<ConstraintF>; 4 * NB] = state.clone();
            for row in 0..4 {
                for col in 0..NB {
                    let ind = row * NB + col;
                    out[ind] = out[ind].xor(&rkey[row][col]).unwrap();
                }
            }

            out
        }

        fn sub_bytes<ConstraintF: PrimeField>(
            state: [UInt8<ConstraintF>; 4 * NB]
        ) -> [UInt8<ConstraintF>; 4 * NB] {
            state.map(|byte: UInt8<ConstraintF>| Aes128Gadget::sub_byte(byte))
        }

        fn shift_rows<ConstraintF: PrimeField>(
            state: [UInt8<ConstraintF>; 4 * NB]
        ) -> [UInt8<ConstraintF>; 4 * NB] {
            [0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11].map(|ind| state[ind].clone())
        }

        fn mix_columns<ConstraintF: PrimeField>(
            state: [UInt8<ConstraintF>; 4 * NB]
        ) -> [UInt8<ConstraintF>; 4 * NB] {
            let mut out = state.clone();
            for row in 0..NB {
                let s0 = state[4 * row].value().unwrap() as usize;
                let s1 = state[4 * row + 1].value().unwrap() as usize;
                let s2 = state[4 * row + 2].value().unwrap() as usize;
                let s3 = state[4 * row + 3].value().unwrap() as usize;

                out[4 * row] = UInt8::constant(MUL2[s0])
                    .xor(&UInt8::constant(MUL3[s1])).unwrap()
                    .xor(&UInt8::constant(s2 as u8)).unwrap()
                    .xor(&UInt8::constant(s3 as u8)).unwrap();
                out[4 * row + 1] = UInt8::constant(s0 as u8)
                    .xor(&UInt8::constant(MUL2[s1])).unwrap()
                    .xor(&UInt8::constant(MUL3[s2])).unwrap()
                    .xor(&UInt8::constant(s3 as u8)).unwrap();
                out[4 * row + 2] = UInt8::constant(s0 as u8)
                    .xor(&UInt8::constant(s1 as u8)).unwrap()
                    .xor(&UInt8::constant(MUL2[s2])).unwrap()
                    .xor(&UInt8::constant(MUL3[s3])).unwrap();
                out[4 * row + 3] = UInt8::constant(MUL3[s0])
                    .xor(&UInt8::constant(s1 as u8)).unwrap()
                    .xor(&UInt8::constant(s2 as u8)).unwrap()
                    .xor(&UInt8::constant(MUL2[s3])).unwrap();
            }
            out
        }

        let mut state: [UInt8<ConstraintF>; 4 * NB] = input.clone();

        state = add_round_key(state.clone(), &rkeys[0..NB]);

        for round in 1..NR {
            state = sub_bytes(state.clone());
            state = shift_rows(state.clone());
            state = mix_columns(state.clone());
            state = add_round_key(state.clone(), &rkeys[round*NB..(round+1)*NB]);
        }

        state = sub_bytes(state.clone());
        state = shift_rows(state);
        state = add_round_key(state, &rkeys[NR*NB..(NR+1)*NB]);

        state
    }
}

/// The unit type for circuit variables. This contains no data.
#[derive(Clone, Debug, Default)]
pub struct RandomnessUnitVar<ConstraintF: PrimeField>(PhantomData<ConstraintF>);

impl<ConstraintF: PrimeField> AllocVar<Randomness, ConstraintF> for RandomnessUnitVar<ConstraintF> {
    // Allocates 32 UInt8s
    fn new_variable<T: Borrow<Randomness>>(
        _cs: impl Into<Namespace<ConstraintF>>,
        _f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Ok(RandomnessUnitVar(PhantomData))
    }
}

/// The unit type for circuit variables. This contains no data.
#[derive(Clone, Debug, Default)]
pub struct ParametersUnitVar<ConstraintF: PrimeField>(PhantomData<ConstraintF>);

impl<ConstraintF: PrimeField> AllocVar<Parameters, ConstraintF> for ParametersUnitVar<ConstraintF> {
    // Allocates 32 UInt8s
    fn new_variable<T: Borrow<Parameters>>(
        _cs: impl Into<Namespace<ConstraintF>>,
        _f: impl FnOnce() -> Result<T, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Ok(ParametersUnitVar(PhantomData))
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "ConstraintF: PrimeField"))]
pub struct PlaintextVar<ConstraintF: PrimeField> {
    pub plaintext: [UInt8<ConstraintF>; 16],
}

impl<ConstraintF: PrimeField> AllocVar<Plaintext, ConstraintF> for PlaintextVar<ConstraintF> {
    fn new_variable<T: Borrow<Plaintext>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let plaintext = f().unwrap().borrow().clone();

        let mut var_bytes: [UInt8<ConstraintF>; 16] = [0u8; 16].map(|x| UInt8::constant(x));
        for i in 0..16 {
            var_bytes[i] = UInt8::new_variable(
                cs.clone(),
                || Ok(plaintext[i]),
                mode
            ).unwrap();
        }

        Ok(Self{
            plaintext: var_bytes
        })
    }
}

#[derive(Derivative)]
#[derivative(Clone(bound = "ConstraintF: PrimeField"))]
pub struct KeyVar<ConstraintF: PrimeField> {
    pub key: [UInt8<ConstraintF>; 16],
}

impl<ConstraintF: PrimeField> AllocVar<Key, ConstraintF> for KeyVar<ConstraintF> {
    fn new_variable<T: Borrow<Key>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let key = f().unwrap().borrow().clone();

        let mut var_bytes: [UInt8<ConstraintF>; 16] = [0u8; 16].map(|x| UInt8::constant(x));
        for i in 0..16 {
            var_bytes[i] = UInt8::new_variable(
                cs.clone(),
                || Ok(key[i]),
                mode
            ).unwrap();
        }

        Ok(Self{
            key: var_bytes
        })
    }
}

#[derive(Derivative, Debug)]
#[derivative(Clone(bound = "ConstraintF: PrimeField"))]
pub struct OutputVar<ConstraintF: PrimeField> {
    pub ciphertext: [UInt8<ConstraintF>; 16],
}

impl<ConstraintF: PrimeField> AllocVar<Ciphertext, ConstraintF> for OutputVar<ConstraintF> {
    fn new_variable<T: Borrow<Ciphertext>>(
        cs: impl Into<Namespace<ConstraintF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let ciphertext = f().unwrap().borrow().clone();

        let mut var_bytes: [UInt8<ConstraintF>; 16] = [0u8; 16].map(|x| UInt8::constant(x));
        for i in 0..16 {
            var_bytes[i] = UInt8::new_variable(
                cs.clone(),
                || Ok(ciphertext[i]),
                mode
            ).unwrap();
        }

        Ok(Self{
            ciphertext: var_bytes
        })
    }
}

impl<ConstraintF: PrimeField> EqGadget<ConstraintF> for OutputVar<ConstraintF> {
    #[inline]
    fn is_eq(&self, other: &Self) -> Result<Boolean<ConstraintF>, SynthesisError> {
        self.ciphertext.is_eq(&other.ciphertext)
    }
}

impl<ConstraintF: PrimeField> SymmetricEncryptionGadget<Aes128, ConstraintF> for Aes128Gadget<ConstraintF> {
    type OutputVar = OutputVar<ConstraintF>;
    type ParametersVar = ParametersUnitVar<ConstraintF>;
    type PlaintextVar = PlaintextVar<ConstraintF>;
    type KeyVar = KeyVar<ConstraintF>;
    type RandomnessVar = RandomnessUnitVar<ConstraintF>;

    fn encrypt(
        _parameters: &Self::ParametersVar,
        message: &Self::PlaintextVar,
        _randomness: &Self::RandomnessVar,
        key: &Self::KeyVar,
    ) -> Result<Self::OutputVar, SynthesisError> {
        let rkeys: [[UInt8<ConstraintF>; 4]; NB * (NR + 1)] = Aes128Gadget::aes128_key_schedule(key.key.clone());
        let ciphertext = Aes128Gadget::aes128_encrypt(message.plaintext.clone(), rkeys);
        Ok(OutputVar{ ciphertext })
    }
}

#[cfg(test)]
#[allow(unused_imports)]
mod aes_test {
    use std::iter::zip;
    use super::*;

    use ark_ed_on_bls12_381::{EdwardsProjective as JubJub, Fr};
    use ark_r1cs_std::R1CSVar;

    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use crate::encryption::{SymmetricEncryptionScheme};
    use crate::encryption::elgamal::constraints::ConstraintF;

    // Keys and Expected Key Schedules from:
    // (1) https://www.samiam.org/key-schedule.html
    // (2) https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf (Appendix A)
    const CIPHER_KEYS: [[u8; 16]; 5] = [
        [ 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, ],
        [ 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, ],
        [ 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, ],
        [ 0x49, 0x20, 0xe2, 0x99, 0xa5, 0x20, 0x52, 0x61, 0x64, 0x69, 0x6f, 0x47, 0x61, 0x74, 0x75, 0x6e, ],
        [ 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c, ],
    ];

    const KEY_SCHEDULES: [[u8; 176]; 5] = [
        [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x62, 0x63, 0x63, 0x63, 0x62, 0x63, 0x63, 0x63, 0x62, 0x63, 0x63, 0x63, 0x62, 0x63, 0x63, 0x63,
            0x9b, 0x98, 0x98, 0xc9, 0xf9, 0xfb, 0xfb, 0xaa, 0x9b, 0x98, 0x98, 0xc9, 0xf9, 0xfb, 0xfb, 0xaa,
            0x90, 0x97, 0x34, 0x50, 0x69, 0x6c, 0xcf, 0xfa, 0xf2, 0xf4, 0x57, 0x33, 0x0b, 0x0f, 0xac, 0x99,
            0xee, 0x06, 0xda, 0x7b, 0x87, 0x6a, 0x15, 0x81, 0x75, 0x9e, 0x42, 0xb2, 0x7e, 0x91, 0xee, 0x2b,
            0x7f, 0x2e, 0x2b, 0x88, 0xf8, 0x44, 0x3e, 0x09, 0x8d, 0xda, 0x7c, 0xbb, 0xf3, 0x4b, 0x92, 0x90,
            0xec, 0x61, 0x4b, 0x85, 0x14, 0x25, 0x75, 0x8c, 0x99, 0xff, 0x09, 0x37, 0x6a, 0xb4, 0x9b, 0xa7,
            0x21, 0x75, 0x17, 0x87, 0x35, 0x50, 0x62, 0x0b, 0xac, 0xaf, 0x6b, 0x3c, 0xc6, 0x1b, 0xf0, 0x9b,
            0x0e, 0xf9, 0x03, 0x33, 0x3b, 0xa9, 0x61, 0x38, 0x97, 0x06, 0x0a, 0x04, 0x51, 0x1d, 0xfa, 0x9f,
            0xb1, 0xd4, 0xd8, 0xe2, 0x8a, 0x7d, 0xb9, 0xda, 0x1d, 0x7b, 0xb3, 0xde, 0x4c, 0x66, 0x49, 0x41,
            0xb4, 0xef, 0x5b, 0xcb, 0x3e, 0x92, 0xe2, 0x11, 0x23, 0xe9, 0x51, 0xcf, 0x6f, 0x8f, 0x18, 0x8e,
        ],
        [
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xe8, 0xe9, 0xe9, 0xe9, 0x17, 0x16, 0x16, 0x16, 0xe8, 0xe9, 0xe9, 0xe9, 0x17, 0x16, 0x16, 0x16,
            0xad, 0xae, 0xae, 0x19, 0xba, 0xb8, 0xb8, 0x0f, 0x52, 0x51, 0x51, 0xe6, 0x45, 0x47, 0x47, 0xf0,
            0x09, 0x0e, 0x22, 0x77, 0xb3, 0xb6, 0x9a, 0x78, 0xe1, 0xe7, 0xcb, 0x9e, 0xa4, 0xa0, 0x8c, 0x6e,
            0xe1, 0x6a, 0xbd, 0x3e, 0x52, 0xdc, 0x27, 0x46, 0xb3, 0x3b, 0xec, 0xd8, 0x17, 0x9b, 0x60, 0xb6,
            0xe5, 0xba, 0xf3, 0xce, 0xb7, 0x66, 0xd4, 0x88, 0x04, 0x5d, 0x38, 0x50, 0x13, 0xc6, 0x58, 0xe6,
            0x71, 0xd0, 0x7d, 0xb3, 0xc6, 0xb6, 0xa9, 0x3b, 0xc2, 0xeb, 0x91, 0x6b, 0xd1, 0x2d, 0xc9, 0x8d,
            0xe9, 0x0d, 0x20, 0x8d, 0x2f, 0xbb, 0x89, 0xb6, 0xed, 0x50, 0x18, 0xdd, 0x3c, 0x7d, 0xd1, 0x50,
            0x96, 0x33, 0x73, 0x66, 0xb9, 0x88, 0xfa, 0xd0, 0x54, 0xd8, 0xe2, 0x0d, 0x68, 0xa5, 0x33, 0x5d,
            0x8b, 0xf0, 0x3f, 0x23, 0x32, 0x78, 0xc5, 0xf3, 0x66, 0xa0, 0x27, 0xfe, 0x0e, 0x05, 0x14, 0xa3,
            0xd6, 0x0a, 0x35, 0x88, 0xe4, 0x72, 0xf0, 0x7b, 0x82, 0xd2, 0xd7, 0x85, 0x8c, 0xd7, 0xc3, 0x26,
        ],
        [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
            0xd6, 0xaa, 0x74, 0xfd, 0xd2, 0xaf, 0x72, 0xfa, 0xda, 0xa6, 0x78, 0xf1, 0xd6, 0xab, 0x76, 0xfe,
            0xb6, 0x92, 0xcf, 0x0b, 0x64, 0x3d, 0xbd, 0xf1, 0xbe, 0x9b, 0xc5, 0x00, 0x68, 0x30, 0xb3, 0xfe,
            0xb6, 0xff, 0x74, 0x4e, 0xd2, 0xc2, 0xc9, 0xbf, 0x6c, 0x59, 0x0c, 0xbf, 0x04, 0x69, 0xbf, 0x41,
            0x47, 0xf7, 0xf7, 0xbc, 0x95, 0x35, 0x3e, 0x03, 0xf9, 0x6c, 0x32, 0xbc, 0xfd, 0x05, 0x8d, 0xfd,
            0x3c, 0xaa, 0xa3, 0xe8, 0xa9, 0x9f, 0x9d, 0xeb, 0x50, 0xf3, 0xaf, 0x57, 0xad, 0xf6, 0x22, 0xaa,
            0x5e, 0x39, 0x0f, 0x7d, 0xf7, 0xa6, 0x92, 0x96, 0xa7, 0x55, 0x3d, 0xc1, 0x0a, 0xa3, 0x1f, 0x6b,
            0x14, 0xf9, 0x70, 0x1a, 0xe3, 0x5f, 0xe2, 0x8c, 0x44, 0x0a, 0xdf, 0x4d, 0x4e, 0xa9, 0xc0, 0x26,
            0x47, 0x43, 0x87, 0x35, 0xa4, 0x1c, 0x65, 0xb9, 0xe0, 0x16, 0xba, 0xf4, 0xae, 0xbf, 0x7a, 0xd2,
            0x54, 0x99, 0x32, 0xd1, 0xf0, 0x85, 0x57, 0x68, 0x10, 0x93, 0xed, 0x9c, 0xbe, 0x2c, 0x97, 0x4e,
            0x13, 0x11, 0x1d, 0x7f, 0xe3, 0x94, 0x4a, 0x17, 0xf3, 0x07, 0xa7, 0x8b, 0x4d, 0x2b, 0x30, 0xc5,
        ],
        [
            0x49, 0x20, 0xe2, 0x99, 0xa5, 0x20, 0x52, 0x61, 0x64, 0x69, 0x6f, 0x47, 0x61, 0x74, 0x75, 0x6e,
            0xda, 0xbd, 0x7d, 0x76, 0x7f, 0x9d, 0x2f, 0x17, 0x1b, 0xf4, 0x40, 0x50, 0x7a, 0x80, 0x35, 0x3e,
            0x15, 0x2b, 0xcf, 0xac, 0x6a, 0xb6, 0xe0, 0xbb, 0x71, 0x42, 0xa0, 0xeb, 0x0b, 0xc2, 0x95, 0xd5,
            0x34, 0x01, 0xcc, 0x87, 0x5e, 0xb7, 0x2c, 0x3c, 0x2f, 0xf5, 0x8c, 0xd7, 0x24, 0x37, 0x19, 0x02,
            0xa6, 0xd5, 0xbb, 0xb1, 0xf8, 0x62, 0x97, 0x8d, 0xd7, 0x97, 0x1b, 0x5a, 0xf3, 0xa0, 0x02, 0x58,
            0x56, 0xa2, 0xd1, 0xbc, 0xae, 0xc0, 0x46, 0x31, 0x79, 0x57, 0x5d, 0x6b, 0x8a, 0xf7, 0x5f, 0x33,
            0x1e, 0x6d, 0x12, 0xc2, 0xb0, 0xad, 0x54, 0xf3, 0xc9, 0xfa, 0x09, 0x98, 0x43, 0x0d, 0x56, 0xab,
            0x89, 0xdc, 0x70, 0xd8, 0x39, 0x71, 0x24, 0x2b, 0xf0, 0x8b, 0x2d, 0xb3, 0xb3, 0x86, 0x7b, 0x18,
            0x4d, 0xfd, 0xdd, 0xb5, 0x74, 0x8c, 0xf9, 0x9e, 0x84, 0x07, 0xd4, 0x2d, 0x37, 0x81, 0xaf, 0x35,
            0x5a, 0x84, 0x4b, 0x2f, 0x2e, 0x08, 0xb2, 0xb1, 0xaa, 0x0f, 0x66, 0x9c, 0x9d, 0x8e, 0xc9, 0xa9,
            0x75, 0x59, 0x98, 0x71, 0x5b, 0x51, 0x2a, 0xc0, 0xf1, 0x5e, 0x4c, 0x5c, 0x6c, 0xd0, 0x85, 0xf5,
        ],
        [
            0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
            0xa0, 0xfa, 0xfe, 0x17, 0x88, 0x54, 0x2c, 0xb1, 0x23, 0xa3, 0x39, 0x39, 0x2a, 0x6c, 0x76, 0x05,
            0xf2, 0xc2, 0x95, 0xf2, 0x7a, 0x96, 0xb9, 0x43, 0x59, 0x35, 0x80, 0x7a, 0x73, 0x59, 0xf6, 0x7f,
            0x3d, 0x80, 0x47, 0x7d, 0x47, 0x16, 0xfe, 0x3e, 0x1e, 0x23, 0x7e, 0x44, 0x6d, 0x7a, 0x88, 0x3b,
            0xef, 0x44, 0xa5, 0x41, 0xa8, 0x52, 0x5b, 0x7f, 0xb6, 0x71, 0x25, 0x3b, 0xdb, 0x0b, 0xad, 0x00,
            0xd4, 0xd1, 0xc6, 0xf8, 0x7c, 0x83, 0x9d, 0x87, 0xca, 0xf2, 0xb8, 0xbc, 0x11, 0xf9, 0x15, 0xbc,
            0x6d, 0x88, 0xa3, 0x7a, 0x11, 0x0b, 0x3e, 0xfd, 0xdb, 0xf9, 0x86, 0x41, 0xca, 0x00, 0x93, 0xfd,
            0x4e, 0x54, 0xf7, 0x0e, 0x5f, 0x5f, 0xc9, 0xf3, 0x84, 0xa6, 0x4f, 0xb2, 0x4e, 0xa6, 0xdc, 0x4f,
            0xea, 0xd2, 0x73, 0x21, 0xb5, 0x8d, 0xba, 0xd2, 0x31, 0x2b, 0xf5, 0x60, 0x7f, 0x8d, 0x29, 0x2f,
            0xac, 0x77, 0x66, 0xf3, 0x19, 0xfa, 0xdc, 0x21, 0x28, 0xd1, 0x29, 0x41, 0x57, 0x5c, 0x00, 0x6e,
            0xd0, 0x14, 0xf9, 0xa8, 0xc9, 0xee, 0x25, 0x89, 0xe1, 0x3f, 0x0c, 0xc8, 0xb6, 0x63, 0x0c, 0xa6,
        ],
    ];

    // Test key expansion method
    #[test]
    fn test_key_expansion() {
        type AesGadget = Aes128Gadget<Fr>;

        for (ck, ks) in zip(CIPHER_KEYS, KEY_SCHEDULES) {
            let cipher_key = ck.map(|byte: u8| UInt8::constant(byte));

            let round_keys: [[UInt8<Fr>; 4]; NB * (NR + 1)] = AesGadget::aes128_key_schedule(cipher_key);

            assert_eq!(round_keys.len(), ks.len() / 4);
            let mut i = 0;
            for word in round_keys {
                for byte in word {
                    assert_eq!(byte.value().unwrap(), ks[i]);
                    i += 1;
                }
            }
        }
    }

    // Test vector for cipher algorithm.
    // Source: https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf (Appendix B)
    const FIPS_197_CIPHERKEY: [u8; 16] = [
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c,
    ];
    const FIPS_197_INPUT: [u8; 16] = [
        0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34,
    ];
    const FIPS_197_OUTPUT: [u8; 16] = [
        0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32,
    ];

    // Test against the step-by-step example detailed in FIPS-197.
    // Source: https://csrc.nist.gov/csrc/media/publications/fips/197/final/documents/fips-197.pdf
    #[test]
    fn test_fips_197_example() {
        let cipher_key: [UInt8<Fr>; 16] = FIPS_197_CIPHERKEY.map(|byte: u8| UInt8::constant(byte));
        let plaintext: [UInt8<Fr>; 16] = FIPS_197_INPUT.map(|byte: u8| UInt8::constant(byte));
        let round_keys: [[UInt8<Fr>; 4]; NB * (NR + 1)] = Aes128Gadget::aes128_key_schedule(cipher_key);
        let ciphertext: [UInt8<Fr>; 16] = Aes128Gadget::aes128_encrypt(plaintext, round_keys);

        assert_eq!(FIPS_197_OUTPUT, ciphertext.map(|byte| byte.value().unwrap()));
    }

    // Test vector for cipher algorithm.
    // Source: http://www.herongyang.com/Cryptography/AES-Example-Vector-of-AES-Encryption.html
    const HERONG_YANG_CIPHERKEY: [u8; 16] = [
        0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    ];
    const HERONG_YANG_INPUT: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0xff,
    ];
    const HERONG_YANG_OUTPUT: [u8; 16] = [
        0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4, 0xc5, 0x5a,
    ];

    // Test against the step-by-step example detailed in the link below.
    // Source: http://www.herongyang.com/Cryptography/AES-Example-Vector-of-AES-Encryption.html
    #[test]
    fn test_herong_yang_example() {
        let cipher_key: [UInt8<Fr>; 16] = HERONG_YANG_CIPHERKEY.map(|byte: u8| UInt8::constant(byte));
        let plaintext: [UInt8<Fr>; 16] = HERONG_YANG_INPUT.map(|byte: u8| UInt8::constant(byte));
        let round_keys: [[UInt8<Fr>; 4]; NB * (NR + 1)] = Aes128Gadget::aes128_key_schedule(cipher_key);
        let ciphertext: [UInt8<Fr>; 16] = Aes128Gadget::aes128_encrypt(plaintext, round_keys);

        assert_eq!(HERONG_YANG_OUTPUT, ciphertext.map(|byte| byte.value().unwrap()));
    }

    #[test]
    fn test_against_rust_crypto_ase() {
        let rng = &mut test_rng();

        type RustCryptoAes = Aes128;
        type MyGadget = Aes128Gadget<Fr>;

        // compute primitive result
        let parameters = RustCryptoAes::setup(rng).unwrap();
        let key = RustCryptoAes::keygen(&parameters, rng).unwrap();
        let mut msg = [0u8; 16];
        rng.fill_bytes(&mut msg);
        let randomness = Randomness {};
        let primitive_result = RustCryptoAes::encrypt(&parameters, &key, &msg, &randomness).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let params_var = ParametersUnitVar::new_constant(ark_relations::ns!(cs, "gadget_parameters"), &parameters).unwrap();
        let msg_var = PlaintextVar::new_witness(ark_relations::ns!(cs, "gadget_message"), || Ok(&msg)).unwrap();
        let random_var = RandomnessUnitVar::new_witness(ark_relations::ns!(cs, "gadget_randomness"), || Ok(&randomness)).unwrap();
        let key_var = KeyVar::new_witness(ark_relations::ns!(cs, "gadget_key"), || Ok(&key)).unwrap();

        // use gadget
        let result_var =
            MyGadget::encrypt(
                &params_var,
                &msg_var,
                &random_var,
                &key_var
            ).unwrap();

        // check that result equals expected ciphertext in the constraint system
        let expected_var =
            <MyGadget as SymmetricEncryptionGadget<RustCryptoAes, Fr>>::OutputVar::new_input(
                ark_relations::ns!(cs, "gadget_expected"),
                || Ok(&primitive_result),
            )
                .unwrap();
        expected_var.enforce_equal(&result_var).unwrap();

        assert_eq!(primitive_result, result_var.ciphertext.value().unwrap().as_slice());
        assert!(cs.is_satisfied().unwrap());
    }
}