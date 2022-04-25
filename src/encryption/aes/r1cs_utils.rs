use std::iter;
use ark_ff::PrimeField;
use ark_r1cs_std::bits::boolean::Boolean;
use ark_r1cs_std::uint64::UInt64;
use ark_relations::r1cs::SynthesisError;

/// Extra traits not automatically implemented by UInt32
pub(crate) trait UInt64Ext<ConstraintF: PrimeField>: Sized {
    /// Right shift
    fn shr(&self, by: usize) -> Self;

    /// Left shift
    fn shl(&self, by: usize) -> Self;

    /// Bitwise AND
    fn bitand(&self, rhs: &Self) -> Result<Self, SynthesisError>;

    /// Bitwise OR
    fn bitor(&self, rhs: &Self) -> Result<Self, SynthesisError>;

    /// Reverse
    fn reverse(&self) -> Self;
}

impl<ConstraintF: PrimeField> UInt64Ext<ConstraintF> for UInt64<ConstraintF> {
    fn shr(&self, by: usize) -> Self {
        assert!(by < 64);

        let zeros = iter::repeat(Boolean::constant(false)).take(by);
        let new_bits: Vec<_> = self
            .to_bits_le()
            .into_iter()
            .skip(by)
            .chain(zeros)
            .collect();
        UInt64::from_bits_le(&new_bits)
    }

    fn shl(&self, by: usize) -> Self {
        assert!(by < 64);

        let zeros = iter::repeat(Boolean::constant(false)).take(by);
        let new_bits: Vec<_> = zeros
            .chain(self
                .to_bits_le()
                .into_iter()
                .take(64 - by))
            .collect();
        UInt64::from_bits_le(&new_bits)
    }

    fn bitand(&self, rhs: &Self) -> Result<Self, SynthesisError> {
        let new_bits: Result<Vec<_>, SynthesisError> = self
            .to_bits_le()
            .into_iter()
            .zip(rhs.to_bits_le().into_iter())
            .map(|(a, b)| a.and(&b))
            .collect();
        Ok(UInt64::from_bits_le(&new_bits?))
    }

    fn bitor(&self, rhs: &Self) -> Result<Self, SynthesisError> {
        let new_bits: Result<Vec<_>, SynthesisError> = self
            .to_bits_le()
            .into_iter()
            .zip(rhs.to_bits_le().into_iter())
            .map(|(a, b)| a.or(&b))
            .collect();
        Ok(UInt64::from_bits_le(&new_bits?))
    }

    fn reverse(&self) -> Self {
        // let new_bits: Vec<_> = self.to_bits_le().iter().map(Boolean::not).collect();
        // UInt32::from_bits_le(&new_bits)
        let mut new_bits: Vec<_>  = self.to_bits_le();
        new_bits.reverse();
        UInt64::from_bits_le(&new_bits)
    }
}

#[cfg(test)]
mod uint_64_ext_test {
    use super::*;

    use ark_bls12_377::Fr;
    use ark_r1cs_std::{bits::uint64::UInt64, R1CSVar};
    use ark_std::rand::Rng;

    const NUM_TESTS: usize = 1_000;

    #[test]
    fn test_shr() {
        let mut rng = ark_std::test_rng();
        for _ in 0..NUM_TESTS {
            let x = rng.gen::<u64>();
            let by = rng.gen::<usize>() % 64;
            assert_eq!(UInt64::<Fr>::constant(x).shr(by).value().unwrap(), x >> by);
        }
    }

    #[test]
    fn test_shl() {
        let mut rng = ark_std::test_rng();
        for _ in 0..NUM_TESTS {
            let x = rng.gen::<u64>();
            let by = rng.gen::<usize>() % 64;
            assert_eq!(UInt64::<Fr>::constant(x).shl(by).value().unwrap(), x << by);
        }
    }

    #[test]
    fn test_bitand() {
        let mut rng = ark_std::test_rng();
        for _ in 0..NUM_TESTS {
            let x = rng.gen::<u64>();
            let y = rng.gen::<u64>();
            assert_eq!(
                UInt64::<Fr>::constant(x)
                    .bitand(&UInt64::constant(y))
                    .unwrap()
                    .value()
                    .unwrap(),
                x & y
            );
        }
    }

    #[test]
    fn test_bitor() {
        let mut rng = ark_std::test_rng();
        for _ in 0..NUM_TESTS {
            let x = rng.gen::<u64>();
            let y = rng.gen::<u64>();
            assert_eq!(
                UInt64::<Fr>::constant(x)
                    .bitor(&UInt64::constant(y))
                    .unwrap()
                    .value()
                    .unwrap(),
                x | y
            );
        }
    }

    #[test]
    fn test_reverse() {
        let mut rng = ark_std::test_rng();
        for _ in 0..NUM_TESTS {
            let x = rng.gen::<u64>();
            assert_eq!(UInt64::<Fr>::constant(x).reverse().value().unwrap(), x.reverse_bits());
        }
    }
}