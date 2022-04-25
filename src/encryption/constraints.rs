use crate::encryption::{AsymmetricEncryptionScheme, SymmetricEncryptionScheme};

use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::SynthesisError;
use core::fmt::Debug;

use ark_ff::fields::Field;

pub trait AsymmetricEncryptionGadget<C: AsymmetricEncryptionScheme, ConstraintF: Field> {
    type OutputVar: AllocVar<C::Ciphertext, ConstraintF>
        + EqGadget<ConstraintF>
        + Clone
        + Sized
        + Debug;
    type ParametersVar: AllocVar<C::Parameters, ConstraintF> + Clone;
    type PlaintextVar: AllocVar<C::Plaintext, ConstraintF> + Clone;
    type PublicKeyVar: AllocVar<C::PublicKey, ConstraintF> + Clone;
    type RandomnessVar: AllocVar<C::Randomness, ConstraintF> + Clone;

    fn encrypt(
        parameters: &Self::ParametersVar,
        message: &Self::PlaintextVar,
        randomness: &Self::RandomnessVar,
        public_key: &Self::PublicKeyVar,
    ) -> Result<Self::OutputVar, SynthesisError>;
}

pub trait SymmetricEncryptionGadget<C: SymmetricEncryptionScheme, ConstraintF: Field> {
    type OutputVar: AllocVar<C::Ciphertext, ConstraintF>
    + EqGadget<ConstraintF>
    + Clone
    + Sized
    + Debug;
    type ParametersVar: AllocVar<C::Parameters, ConstraintF> + Clone;
    type PlaintextVar: AllocVar<C::Plaintext, ConstraintF> + Clone;
    type KeyVar: AllocVar<C::Key, ConstraintF> + Clone;
    type RandomnessVar: AllocVar<C::Randomness, ConstraintF> + Clone;

    fn encrypt(
        parameters: &Self::ParametersVar,
        message: &Self::PlaintextVar,
        randomness: &Self::RandomnessVar,
        public_key: &Self::KeyVar,
    ) -> Result<Self::OutputVar, SynthesisError>;
}
