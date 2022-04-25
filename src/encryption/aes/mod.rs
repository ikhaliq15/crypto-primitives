use ark_std::rand::Rng;
use aes::{Aes128 as ExternalAes128, Block, BlockDecrypt, BlockEncrypt, NewBlockCipher};
use digest::generic_array::GenericArray;
use crate::encryption::SymmetricEncryptionScheme;
use crate::Error;

#[cfg(feature = "r1cs")]
mod r1cs_utils;

#[cfg(feature = "r1cs")]
pub mod constraints;

pub struct Aes128 {}

pub struct Parameters {}

pub type Key = [u8; 16];

pub struct Randomness {}

pub type Plaintext = [u8; 16];

pub type Ciphertext = [u8; 16];

impl SymmetricEncryptionScheme for Aes128 {
    type Parameters = Parameters;
    type Key = Key;
    type Randomness = Randomness;
    type Plaintext = Plaintext;
    type Ciphertext = Ciphertext;

    fn setup<R: Rng>(_rng: &mut R) -> Result<Self::Parameters, Error> {
        Ok(Parameters { })
    }

    fn keygen<R: Rng>(
        _pp: &Self::Parameters,
        rng: &mut R,
    ) -> Result<Self::Key, Error> {
        // get a random element from the scalar field
        let mut key = vec![0u8; 16];
        rng.fill_bytes(&mut key);
        let mut key_bytes: [u8; 16] = Default::default();
        key_bytes.copy_from_slice(key.as_slice());
        Ok(key_bytes)
    }

    fn encrypt(
        _pp: &Self::Parameters,
        key: &Self::Key,
        message: &Self::Plaintext,
        _r: &Self::Randomness,
    ) -> Result<Self::Ciphertext, Error> {
        let aes = ExternalAes128::new(&GenericArray::from(*key));
        let mut block: Block = Block::from(*message);
        aes.encrypt_block(&mut block);
        let mut ciphertext: Ciphertext = Default::default();
        ciphertext.copy_from_slice(block.as_slice());
        Ok(ciphertext)
    }

    fn decrypt(
        _pp: &Self::Parameters,
        key: &Self::Key,
        ciphertext: &Self::Ciphertext,
    ) -> Result<Self::Plaintext, Error> {
        let aes = ExternalAes128::new(&GenericArray::from(*key));
        let mut block: Block = Block::from(*ciphertext);
        aes.decrypt_block(&mut block);
        let mut message: Plaintext = Default::default();
        message.copy_from_slice(block.as_slice());
        Ok(message)
    }
}

#[cfg(test)]
mod test_aes {
    use ark_std::{test_rng};

    use ark_std::rand::RngCore;
    use crate::encryption::aes::{Aes128, Randomness};

    use crate::encryption::{SymmetricEncryptionScheme};

    #[test]
    fn test_aes_encryption() {
        let rng = &mut test_rng();

        // setup and key generation
        let parameters = Aes128::setup(rng).unwrap();
        let key = Aes128::keygen(&parameters, rng).unwrap();

        // get a random msg and encryption randomness
        let mut msg = [0u8; 16];
        rng.fill_bytes(&mut msg);
        let r = Randomness{};

        // encrypt and decrypt the message
        let cipher = Aes128::encrypt(&parameters, &key, &msg, &r).unwrap();
        let check_msg = Aes128::decrypt(&parameters, &key, &cipher).unwrap();

        assert_eq!(msg, check_msg);
    }
}