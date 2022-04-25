// TODO: add credits/sources.

use std::borrow::Borrow;
use std::iter;
use std::marker::PhantomData;
use ark_ff::{PrimeField};
use ark_r1cs_std::{ToBitsGadget, ToBytesGadget};
use ark_r1cs_std::alloc::{AllocationMode, AllocVar};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::uint8::UInt8;
use ark_relations::r1cs::{Namespace, SynthesisError};
use crate::encryption::aes::{Aes128, Ciphertext, Key, Parameters, Plaintext, r1cs_utils::UInt64Ext, Randomness};
use crate::encryption::SymmetricEncryptionGadget;

pub type AesState<ConstraintF> = [UInt64<ConstraintF>; 8];
pub type AesRoundKey<ConstraintF> = [UInt64<ConstraintF>; 8]; // TODO: use this?

#[allow(dead_code)]
pub struct Aes128Gadget<ConstraintF: PrimeField> {
    t: UInt8<ConstraintF>
}

macro_rules! define_mix_columns {
    (
        $name:ident,
        $first_rotate:path,
        $second_rotate:path,
        $state_type:path,
    ) => {
        #[rustfmt::skip]
        fn $name(state: &mut $state_type) {
            let (a0, a1, a2, a3, a4, a5, a6, a7) = (
                state[0].clone(), state[1].clone(), state[2].clone(), state[3].clone(), state[4].clone(), state[5].clone(), state[6].clone(), state[7].clone()
            );
            let (b0, b1, b2, b3, b4, b5, b6, b7) = (
                $first_rotate(a0.clone()),
                $first_rotate(a1.clone()),
                $first_rotate(a2.clone()),
                $first_rotate(a3.clone()),
                $first_rotate(a4.clone()),
                $first_rotate(a5.clone()),
                $first_rotate(a6.clone()),
                $first_rotate(a7.clone()),
            );
            let (c0, c1, c2, c3, c4, c5, c6, c7) = (
                a0.xor(&b0).unwrap(),
                a1.xor(&b1).unwrap(),
                a2.xor(&b2).unwrap(),
                a3.xor(&b3).unwrap(),
                a4.xor(&b4).unwrap(),
                a5.xor(&b5).unwrap(),
                a6.xor(&b6).unwrap(),
                a7.xor(&b7).unwrap(),
            );
            state[0] = b0                      .xor(&c7).unwrap()  .xor(&$second_rotate(c0.clone())).unwrap();
            state[1] = b1  .xor(&c0).unwrap()  .xor(&c7).unwrap()  .xor(&$second_rotate(c1.clone())).unwrap();
            state[2] = b2  .xor(&c1).unwrap()                      .xor(&$second_rotate(c2.clone())).unwrap();
            state[3] = b3  .xor(&c2).unwrap()  .xor(&c7).unwrap()  .xor(&$second_rotate(c3.clone())).unwrap();
            state[4] = b4  .xor(&c3).unwrap()  .xor(&c7).unwrap()  .xor(&$second_rotate(c4.clone())).unwrap();
            state[5] = b5  .xor(&c4).unwrap()                      .xor(&$second_rotate(c5.clone())).unwrap();
            state[6] = b6  .xor(&c5).unwrap()                      .xor(&$second_rotate(c6.clone())).unwrap();
            state[7] = b7  .xor(&c6).unwrap()                      .xor(&$second_rotate(c7.clone())).unwrap();
        }
    }
}

#[allow(dead_code)]
impl<ConstraintF: PrimeField> Aes128Gadget<ConstraintF> {
    /// Fully bitsliced AES-128 key schedule to match the fully-fixsliced representation.
    #[allow(unused_variables, unused_mut)]
    pub fn aes128_key_schedule(key: [UInt8<ConstraintF>; 16]) -> Vec<UInt64<ConstraintF>> {
        let mut rkeys: Vec<UInt64<_>> = std::iter::repeat_with(|| UInt64::constant(0u64)).take(88).collect();
        // let mut rkeys = [0u64; 88].map(UInt64::constant);

        Self::bitslice(&mut rkeys[..8], &key, &key, &key, &key);

        let mut rk_off = 0;
        for rcon in 0..10 {
            Self::memshift32(&mut rkeys, rk_off);
            rk_off += 8;

            Self::sub_bytes(&mut rkeys[rk_off..(rk_off + 8)]);
            Self::sub_bytes_nots(&mut rkeys[rk_off..(rk_off + 8)]);

            if rcon < 8 {
                Self::add_round_constant_bit(&mut rkeys[rk_off..(rk_off + 8)], rcon);
            } else {
                Self::add_round_constant_bit(&mut rkeys[rk_off..(rk_off + 8)], rcon - 8);
                Self::add_round_constant_bit(&mut rkeys[rk_off..(rk_off + 8)], rcon - 7);
                Self::add_round_constant_bit(&mut rkeys[rk_off..(rk_off + 8)], rcon - 5);
                Self::add_round_constant_bit(&mut rkeys[rk_off..(rk_off + 8)], rcon - 4);
            }

            Self::xor_columns(&mut rkeys, rk_off, 8, Self::ror_distance(1, 3));
        }

        // Adjust to match fixslicing format
        #[cfg(feature = "compact")]
        {
            for i in (8..88).step_by(16) {
                inv_shift_rows_1(&mut rkeys[i..(i + 8)]);
            }
        }
        #[cfg(not(feature = "compact"))]
        {
            for i in (8..72).step_by(32) {
                Self::inv_shift_rows_1(&mut rkeys[i..(i + 8)]);
                Self::inv_shift_rows_2(&mut rkeys[(i + 8)..(i + 16)]);
                Self::inv_shift_rows_3(&mut rkeys[(i + 16)..(i + 24)]);
            }
            Self::inv_shift_rows_1(&mut rkeys[72..80]);
        }

        // Account for NOTs removed from sub_bytes
        for i in 1..11 {
            Self::sub_bytes_nots(&mut rkeys[(i * 8)..(i * 8 + 8)]);
        }

        rkeys
    }

    pub fn aes128_encrypt(rkeys: &Vec<UInt64<ConstraintF>>, blocks: &mut [[UInt8<ConstraintF>; 16]]) {
        debug_assert_eq!(rkeys.len(), 88);
        debug_assert_eq!(blocks.len(), 4);
        let mut state: AesState<ConstraintF> = [0u64; 8].map(UInt64::constant);

        Self::bitslice(&mut state, &blocks[0], &blocks[1], &blocks[2], &blocks[3]);

        Self::add_round_key(&mut state, &rkeys[..8]);

        let mut rk_off = 8;
        loop {
            Self::sub_bytes(&mut state);
            Self::mix_columns_1(&mut state);
            Self::add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
            rk_off += 8;

            if rk_off == 80 {
                break;
            }

            #[cfg(not(feature = "compact"))]
            {
                Self::sub_bytes(&mut state);
                Self::mix_columns_2(&mut state);
                Self::add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
                rk_off += 8;

                Self::sub_bytes(&mut state);
                Self::mix_columns_3(&mut state);
                Self::add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
                rk_off += 8;
            }

            Self::sub_bytes(&mut state);
            Self::mix_columns_0(&mut state);
            Self::add_round_key(&mut state, &rkeys[rk_off..(rk_off + 8)]);
            rk_off += 8;
        }

        #[cfg(not(feature = "compact"))]
        {
            Self::shift_rows_2(&mut state);
        }

        Self::sub_bytes(&mut state);
        Self::add_round_key(&mut state, &rkeys[80..]);

        Self::inv_bitslice(&state, blocks);
    }

    fn sub_bytes(state: &mut [UInt64<ConstraintF>], ) {
        debug_assert_eq!(state.len(), 8);

        let u7 = state[0].clone();
        let u6 = state[1].clone();
        let u5 = state[2].clone();
        let u4 = state[3].clone();
        let u3 = state[4].clone();
        let u2 = state[5].clone();
        let u1 = state[6].clone();
        let u0 = state[7].clone();

        let y14 = u3.xor(&u5).unwrap();
        let y13 = u0.xor(&u6).unwrap();
        let y12 = y13.xor(&y14).unwrap();
        let t1 = u4.xor(&y12).unwrap();
        let y15 = t1.xor(&u5).unwrap();
        let t2 = y12.bitand(&y15).unwrap();
        let y6 = y15.xor(&u7).unwrap();
        let y20 = t1.xor(&u1).unwrap();
        // y12 -> stack
        let y9 = u0.xor(&u3).unwrap();
        // y20 -> stack
        let y11 = y20.xor(&y9).unwrap();
        // y9 -> stack
        let t12 = y9.bitand(&y11).unwrap();
        // y6 -> stack
        let y7 = u7.xor(&y11).unwrap();
        let y8 = u0.xor(&u5).unwrap();
        let t0 = u1.xor(&u2).unwrap();
        let y10 = y15.xor(&t0).unwrap();
        // y15 -> stack
        let y17 = y10.xor(&y11).unwrap();
        // y14 -> stack
        let t13 = y14.bitand(&y17).unwrap();
        let t14 = t13.xor(&t12).unwrap();
        // y17 -> stack
        let y19 = y10.xor(&y8).unwrap();
        // y10 -> stack
        let t15 = y8.bitand(&y10).unwrap();
        let t16 = t15.xor(&t12).unwrap();
        let y16 = t0.xor(&y11).unwrap();
        // y11 -> stack
        let y21 = y13.xor(&y16).unwrap();
        // y13 -> stack
        let t7 = y13.bitand(&y16).unwrap();
        // y16 -> stack
        let y18 = u0.xor(&y16).unwrap();
        let y1 = t0.xor(&u7).unwrap();
        let y4 = y1.xor(&u3).unwrap();
        // u7 -> stack
        let t5 = y4.bitand(&u7).unwrap();
        let t6 = t5.xor(&t2).unwrap();
        let t18 = t6.xor(&t16).unwrap();
        let t22 = t18.xor(&y19).unwrap();
        let y2 = y1.xor(&u0).unwrap();
        let t10 = y2.bitand(&y7).unwrap();
        let t11 = t10.xor(&t7).unwrap();
        let t20 = t11.xor(&t16).unwrap();
        let t24 = t20.xor(&y18).unwrap();
        let y5 = y1.xor(&u6).unwrap();
        let t8 = y5.bitand(&y1).unwrap();
        let t9 = t8.xor(&t7).unwrap();
        let t19 = t9.xor(&t14).unwrap();
        let t23 = t19.xor(&y21).unwrap();
        let y3 = y5.xor(&y8).unwrap();
        // y6 <- stack
        let t3 = y3.bitand(&y6).unwrap();
        let t4 = t3.xor(&t2).unwrap();
        // y20 <- stack
        let t17 = t4.xor(&y20).unwrap();
        let t21 = t17.xor(&t14).unwrap();
        let t26 = t21.bitand(&t23).unwrap();
        let t27 = t24.xor(&t26).unwrap();
        let t31 = t22.xor(&t26).unwrap();
        let t25 = t21.xor(&t22).unwrap();
        // y4 -> stack
        let t28 = t25.bitand(&t27).unwrap();
        let t29 = t28.xor(&t22).unwrap();
        let z14 = t29.bitand(&y2).unwrap();
        let z5 = t29.bitand(&y7).unwrap();
        let t30 = t23.xor(&t24).unwrap();
        let t32 = t31.bitand(&t30).unwrap();
        let t33 = t32.xor(&t24).unwrap();
        let t35 = t27.xor(&t33).unwrap();
        let t36 = t24.bitand(&t35).unwrap();
        let t38 = t27.xor(&t36).unwrap();
        let t39 = t29.bitand(&t38).unwrap();
        let t40 = t25.xor(&t39).unwrap();
        let t43 = t29.xor(&t40).unwrap();
        // y16 <- stack
        let z3 = t43.bitand(&y16).unwrap();
        let tc12 = z3.xor(&z5).unwrap();
        // tc12 -> stack
        // y13 <- stack
        let z12 = t43.bitand(&y13).unwrap();
        let z13 = t40.bitand(&y5).unwrap();
        let z4 = t40.bitand(&y1).unwrap();
        let tc6 = z3.xor(&z4).unwrap();
        let t34 = t23.xor(&t33).unwrap();
        let t37 = t36.xor(&t34).unwrap();
        let t41 = t40.xor(&t37).unwrap();
        // y10 <- stack
        let z8 = t41.bitand(&y10).unwrap();
        let z17 = t41.bitand(&y8).unwrap();
        let t44 = t33.xor(&t37).unwrap();
        // y15 <- stack
        let z0 = t44.bitand(&y15).unwrap();
        // z17 -> stack
        // y12 <- stack
        let z9 = t44.bitand(&y12).unwrap();
        let z10 = t37.bitand(&y3).unwrap();
        let z1 = t37.bitand(&y6).unwrap();
        let tc5 = z1.xor(&z0).unwrap();
        let tc11 = tc6.xor(&tc5).unwrap();
        // y4 <- stack
        let z11 = t33.bitand(&y4).unwrap();
        let t42 = t29.xor(&t33).unwrap();
        let t45 = t42.xor(&t41).unwrap();
        // y17 <- stack
        let z7 = t45.bitand(&y17).unwrap();
        let tc8 = z7.xor(&tc6).unwrap();
        // y14 <- stack
        let z16 = t45.bitand(&y14).unwrap();
        // y11 <- stack
        let z6 = t42.bitand(&y11).unwrap();
        let tc16 = z6.xor(&tc8).unwrap();
        // z14 -> stack
        // y9 <- stack
        let z15 = t42.bitand(&y9).unwrap();
        let tc20 = z15.xor(&tc16).unwrap();
        let tc1 = z15.xor(&z16).unwrap();
        let tc2 = z10.xor(&tc1).unwrap();
        let tc21 = tc2.xor(&z11).unwrap();
        let tc3 = z9.xor(&tc2).unwrap();
        let s0 = tc3.xor(&tc16).unwrap();
        let s3 = tc3.xor(&tc11).unwrap();
        let s1 = s3.xor(&tc16).unwrap();
        let tc13 = z13.xor(&tc1).unwrap();
        // u7 <- stack
        let z2 = t33.bitand(&u7).unwrap();
        let tc4 = z0.xor(&z2).unwrap();
        let tc7 = z12.xor(&tc4).unwrap();
        let tc9 = z8.xor(&tc7).unwrap();
        let tc10 = tc8.xor(&tc9).unwrap();
        // z14 <- stack
        let tc17 = z14.xor(&tc10).unwrap();
        let s5 = tc21.xor(&tc17).unwrap();
        let tc26 = tc17.xor(&tc20).unwrap();
        // z17 <- stack
        let s2 = tc26.xor(&z17).unwrap();
        // tc12 <- stack
        let tc14 = tc4.xor(&tc12).unwrap();
        let tc18 = tc13.xor(&tc14).unwrap();
        let s6 = tc10.xor(&tc18).unwrap();
        let s7 = z12.xor(&tc18).unwrap();
        let s4 = tc14.xor(&s3).unwrap();

        state[0] = s7;
        state[1] = s6;
        state[2] = s5;
        state[3] = s4;
        state[4] = s3;
        state[5] = s2;
        state[6] = s1;
        state[7] = s0;
    }

    #[inline]
    fn sub_bytes_nots(state: &mut [UInt64<ConstraintF>]) {
        debug_assert_eq!(state.len(), 8);
        state[0] = state[0].xor(&UInt64::constant(0xffffffffffffffff)).unwrap();
        state[1] = state[1].xor(&UInt64::constant(0xffffffffffffffff)).unwrap();
        state[5] = state[5].xor(&UInt64::constant(0xffffffffffffffff)).unwrap();
        state[6] = state[6].xor(&UInt64::constant(0xffffffffffffffff)).unwrap();
    }

    fn memshift32(buffer: &mut [UInt64<ConstraintF>], src_offset: usize) {
        debug_assert_eq!(src_offset % 8, 0);

        let dst_offset = src_offset + 8;
        debug_assert!(dst_offset + 8 <= buffer.len());

        for i in (0..8).rev() {
            buffer[dst_offset + i] = buffer[src_offset + i].clone();
        }
    }

    fn add_round_key(state: &mut AesState<ConstraintF>, rkey: &[UInt64<ConstraintF>]) {
        debug_assert_eq!(rkey.len(), 8);
        for (a, b) in state.iter_mut().zip(rkey) {
            *a = (*a).xor(b).unwrap();
        }
    }

    #[inline(always)]
    fn add_round_constant_bit(state: &mut [UInt64<ConstraintF>], bit: usize) {
        state[bit] = state[bit].xor(&UInt64::constant(0x00000000f0000000)).unwrap();
    }

    #[inline(always)]
    fn inv_shift_rows_1(state: &mut [UInt64<ConstraintF>]) {
        Self::shift_rows_3(state);
    }

    #[inline(always)]
    fn inv_shift_rows_2(state: &mut [UInt64<ConstraintF>]) {
        Self::shift_rows_2(state);
    }

    #[cfg(not(feature = "compact"))]
    #[inline(always)]
    fn inv_shift_rows_3(state: &mut [UInt64<ConstraintF>]) {
        Self::shift_rows_1(state);
    }

    fn xor_columns(rkeys: &mut [UInt64<ConstraintF>], offset: usize, idx_xor: usize, idx_ror: u32) {
        for i in 0..8 {
            let off_i = offset + i;
            let rk = rkeys[off_i - idx_xor].xor(&(UInt64::constant(0x000f000f000f000f).bitand(&Self::ror(rkeys[off_i].clone(), idx_ror)).unwrap())).unwrap();
            rkeys[off_i] = rk
                .xor(&(UInt64::constant(0xfff0fff0fff0fff0).bitand(&rk.shl(4)).unwrap())).unwrap()
                .xor(&(UInt64::constant(0xff00ff00ff00ff00).bitand(&rk.shl(8)).unwrap())).unwrap()
                .xor(&(UInt64::constant(0xf000f000f000f000).bitand(&rk.shl(12)).unwrap())).unwrap();
        }
    }

    fn bitslice(
        output: &mut [UInt64<ConstraintF>],
        input0: &[UInt8<ConstraintF>],
        input1: &[UInt8<ConstraintF>],
        input2: &[UInt8<ConstraintF>],
        input3: &[UInt8<ConstraintF>])
    {
        debug_assert_eq!(output.len(), 8);
        debug_assert_eq!(input0.len(), 16);
        debug_assert_eq!(input1.len(), 16);
        debug_assert_eq!(input2.len(), 16);
        debug_assert_eq!(input3.len(), 16);

        fn to_uint64<ConstraintF: PrimeField>(input: UInt8<ConstraintF>) -> UInt64<ConstraintF> {
            // TODO: make sure zeroes are added to the correct positions
            let mut byte_bits = input.to_bits_le().unwrap();
            let mut zeros: Vec<_> = iter::repeat(Boolean::constant(false)).take(56).collect();
            byte_bits.append(&mut zeros);
            UInt64::from_bits_le(&byte_bits)
        }

        #[rustfmt::skip]
        fn read_reordered<ConstraintF: PrimeField>(input: &[UInt8<ConstraintF>]) -> UInt64<ConstraintF> {
            (to_uint64(input[0x0].clone())).bitor(
            &(to_uint64(input[0x1].clone()))).unwrap().shl(0x10).bitor(
            &(to_uint64(input[0x2].clone()))).unwrap().shl(0x20).bitor(
            &(to_uint64(input[0x3].clone()))).unwrap().shl(0x30).bitor(
            &(to_uint64(input[0x8].clone()))).unwrap().shl(0x08).bitor(
            &(to_uint64(input[0x9].clone()))).unwrap().shl(0x18).bitor(
            &(to_uint64(input[0xa].clone()))).unwrap().shl(0x28).bitor(
            &(to_uint64(input[0xb].clone()))).unwrap().shl(0x38)
        }

        // Reorder each block's bytes on input
        //     __ __ c1 c0 r1 r0 __ __ __ => __ __ c0 r1 r0 c1 __ __ __
        // Reorder by relabeling (note the order of input)
        //     b1 b0 c0 __ __ __ __ __ __ => c0 b1 b0 __ __ __ __ __ __
        let mut t0 = read_reordered(&input0[0x00..0x0c]);
        let mut t4 = read_reordered(&input0[0x04..0x10]);
        let mut t1 = read_reordered(&input1[0x00..0x0c]);
        let mut t5 = read_reordered(&input1[0x04..0x10]);
        let mut t2 = read_reordered(&input2[0x00..0x0c]);
        let mut t6 = read_reordered(&input2[0x04..0x10]);
        let mut t3 = read_reordered(&input3[0x00..0x0c]);
        let mut t7 = read_reordered(&input3[0x04..0x10]);

        // Bit Index Swap 6 <-> 0:
        //     __ __ b0 __ __ __ __ __ p0 => __ __ p0 __ __ __ __ __ b0
        let m0 = UInt64::constant(0x5555555555555555);
        Self::delta_swap_2(&mut t1, &mut t0, 1, m0.clone());
        Self::delta_swap_2(&mut t3, &mut t2, 1, m0.clone());
        Self::delta_swap_2(&mut t5, &mut t4, 1, m0.clone());
        Self::delta_swap_2(&mut t7, &mut t6, 1, m0.clone());

        // Bit Index Swap 7 <-> 1:
        //     __ b1 __ __ __ __ __ p1 __ => __ p1 __ __ __ __ __ b1 __
        let m1 =  UInt64::constant(0x3333333333333333);
        Self::delta_swap_2(&mut t2, &mut t0, 2, m1.clone());
        Self::delta_swap_2(&mut t3, &mut t1, 2, m1.clone());
        Self::delta_swap_2(&mut t6, &mut t4, 2, m1.clone());
        Self::delta_swap_2(&mut t7, &mut t5, 2, m1.clone());

        // Bit Index Swap 8 <-> 2:
        //     c0 __ __ __ __ __ p2 __ __ => p2 __ __ __ __ __ c0 __ __
        let m2 = UInt64::constant(0x0f0f0f0f0f0f0f0f);
        Self::delta_swap_2(&mut t4, &mut t0, 4, m2.clone());
        Self::delta_swap_2(&mut t5, &mut t1, 4, m2.clone());
        Self::delta_swap_2(&mut t6, &mut t2, 4, m2.clone());
        Self::delta_swap_2(&mut t7, &mut t3, 4, m2.clone());

        // Final bitsliced bit index, as desired:
        //     p2 p1 p0 r1 r0 c1 c0 b1 b0
        output[0] = t0;
        output[1] = t1;
        output[2] = t2;
        output[3] = t3;
        output[4] = t4;
        output[5] = t5;
        output[6] = t6;
        output[7] = t7;
    }

    fn inv_bitslice(input: &[UInt64<ConstraintF>], output: &mut [[UInt8<ConstraintF>; 16]]) {
        debug_assert_eq!(input.len(), 8);
        debug_assert_eq!(output.len(), 4);

        // Unbitslicing is a bit index manipulation. 512 bits of data means each bit is positioned at
        // a 9-bit index. AES data is 4 blocks, each one a 4x4 column-major matrix of bytes, so the
        // desired index for the output is ([b]lock, [c]olumn, [r]ow, [p]osition):
        //     b1 b0 c1 c0 r1 r0 p2 p1 p0
        //
        // The initially bitsliced data groups first by bit position, then row, column, block:
        //     p2 p1 p0 r1 r0 c1 c0 b1 b0

        let mut t0 = input[0].clone();
        let mut t1 = input[1].clone();
        let mut t2 = input[2].clone();
        let mut t3 = input[3].clone();
        let mut t4 = input[4].clone();
        let mut t5 = input[5].clone();
        let mut t6 = input[6].clone();
        let mut t7 = input[7].clone();

        // TODO: these bit index swaps are identical to those in 'packing'

        // Bit Index Swap 6 <-> 0:
        //     __ __ p0 __ __ __ __ __ b0 => __ __ b0 __ __ __ __ __ p0
        let m0 = UInt64::constant(0x5555555555555555);
        Self::delta_swap_2(&mut t1, &mut t0, 1, m0.clone());
        Self::delta_swap_2(&mut t3, &mut t2, 1, m0.clone());
        Self::delta_swap_2(&mut t5, &mut t4, 1, m0.clone());
        Self::delta_swap_2(&mut t7, &mut t6, 1, m0.clone());

        // Bit Index Swap 7 <-> 1:
        //     __ p1 __ __ __ __ __ b1 __ => __ b1 __ __ __ __ __ p1 __
        let m1 = UInt64::constant(0x3333333333333333);
        Self::delta_swap_2(&mut t2, &mut t0, 2, m1.clone());
        Self::delta_swap_2(&mut t3, &mut t1, 2, m1.clone());
        Self::delta_swap_2(&mut t6, &mut t4, 2, m1.clone());
        Self::delta_swap_2(&mut t7, &mut t5, 2, m1.clone());

        // Bit Index Swap 8 <-> 2:
        //     p2 __ __ __ __ __ c0 __ __ => c0 __ __ __ __ __ p2 __ __
        let m2 = UInt64::constant(0x0f0f0f0f0f0f0f0f);
        Self::delta_swap_2(&mut t4, &mut t0, 4, m2.clone());
        Self::delta_swap_2(&mut t5, &mut t1, 4, m2.clone());
        Self::delta_swap_2(&mut t6, &mut t2, 4, m2.clone());
        Self::delta_swap_2(&mut t7, &mut t3, 4, m2.clone());

        #[rustfmt::skip]
        fn write_reordered<ConstraintF: PrimeField>(columns: UInt64<ConstraintF>, output: &mut [UInt8<ConstraintF>]) {
            let column_bytes = columns.to_bytes().unwrap();
            output[0x0] = (column_bytes.get(0)).unwrap().clone();
            output[0x1] = (column_bytes.get(2)).unwrap().clone(); // (columns >> 0x10) as u8;
            output[0x2] = (column_bytes.get(4)).unwrap().clone(); // (columns >> 0x20) as u8;
            output[0x3] = (column_bytes.get(6)).unwrap().clone(); // (columns >> 0x30) as u8;
            output[0x8] = (column_bytes.get(1)).unwrap().clone(); // (columns >> 0x08) as u8;
            output[0x9] = (column_bytes.get(3)).unwrap().clone(); // (columns >> 0x18) as u8;
            output[0xa] = (column_bytes.get(5)).unwrap().clone(); // (columns >> 0x28) as u8;
            output[0xb] = (column_bytes.get(7)).unwrap().clone(); // (columns >> 0x38) as u8;
        }

        // Reorder by relabeling (note the order of output)
        //     c0 b1 b0 __ __ __ __ __ __ => b1 b0 c0 __ __ __ __ __ __
        // Reorder each block's bytes on output
        //     __ __ c0 r1 r0 c1 __ __ __ => __ __ c1 c0 r1 r0 __ __ __
        write_reordered(t0, &mut output[0][0x00..0x0c]);
        write_reordered(t4, &mut output[0][0x04..0x10]);
        write_reordered(t1, &mut output[1][0x00..0x0c]);
        write_reordered(t5, &mut output[1][0x04..0x10]);
        write_reordered(t2, &mut output[2][0x00..0x0c]);
        write_reordered(t6, &mut output[2][0x04..0x10]);
        write_reordered(t3, &mut output[3][0x00..0x0c]);
        write_reordered(t7, &mut output[3][0x04..0x10]);

        // Final AES bit index, as desired:
        //     b1 b0 c1 c0 r1 r0 p2 p1 p0
    }

    #[inline]
    fn delta_swap_1(a: &mut UInt64<ConstraintF>, shift: u32, mask: UInt64<ConstraintF>) {
        let t = ((*a).xor(&((*a).shr(shift as usize))).unwrap()).bitand(&mask).unwrap();
        *a = (*a).xor(&(t.xor(&(t.shl(shift as usize))).unwrap())).unwrap();
    }

    #[inline]
    fn delta_swap_2(a: &mut UInt64<ConstraintF>, b: &mut UInt64<ConstraintF>, shift: u32, mask: UInt64<ConstraintF>) {
        let t = ((*a).xor(&((*b).shr(shift as usize))).unwrap()).bitand(&mask).unwrap();
        *a = (*a).xor(&t).unwrap();
        *b = (*b).xor(&(t.shl(shift as usize))).unwrap();
    }

    /// Applies ShiftRows once on an AES state (or key).
    #[cfg(any(not(feature = "compact"), feature = "hazmat"))]
    #[inline]
    fn shift_rows_1(state: &mut [UInt64<ConstraintF>]) {
        debug_assert_eq!(state.len(), 8);
        for x in state.iter_mut() {
            Self::delta_swap_1(x, 8, UInt64::constant(0x00f000ff000f0000));
            Self::delta_swap_1(x, 4, UInt64::constant(0x0f0f00000f0f0000));
        }
    }

    /// Applies ShiftRows twice on an AES state (or key).
    #[inline]
    fn shift_rows_2(state: &mut [UInt64<ConstraintF>]) {
        debug_assert_eq!(state.len(), 8);
        for x in state.iter_mut() {
            Self::delta_swap_1(x, 8, UInt64::constant(0x00ff000000ff0000));
        }
    }

    /// Applies ShiftRows three times on an AES state (or key).
    #[inline]
    fn shift_rows_3(state: &mut [UInt64<ConstraintF>]) {
        debug_assert_eq!(state.len(), 8);
        for x in state.iter_mut() {
            Self::delta_swap_1(x, 8, UInt64::constant(0x000f00ff00f00000));
            Self::delta_swap_1(x, 4, UInt64::constant(0x0f0f00000f0f0000));
        }
    }

    #[inline(always)]
    fn ror(x: UInt64<ConstraintF>, y: u32) -> UInt64<ConstraintF> {
        x.rotr(y as usize)
    }

    #[inline(always)]
    fn ror_distance(rows: u32, cols: u32) -> u32 {
        (rows << 4) + (cols << 2)
    }

    #[inline(always)]
    fn rotate_rows_1(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        Self::ror(x, Self::ror_distance(1, 0))
    }

    #[inline(always)]
    fn rotate_rows_2(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        Self::ror(x, Self::ror_distance(2, 0))
    }

    #[inline(always)]
    #[rustfmt::skip]
    fn rotate_rows_and_columns_1_1(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        (Self::ror(x.clone(), Self::ror_distance(1, 1)).bitand(&UInt64::constant(0x0fff0fff0fff0fff)).unwrap()).bitor(
            &(Self::ror(x, Self::ror_distance(0, 1)).bitand(&UInt64::constant(0xf000f000f000f000)).unwrap())).unwrap()
    }

    #[cfg(not(feature = "compact"))]
    #[inline(always)]
    #[rustfmt::skip]
    fn rotate_rows_and_columns_1_2(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        (Self::ror(x.clone(), Self::ror_distance(1, 2)).bitand(&UInt64::constant(0x00ff00ff00ff00ff)).unwrap()).bitor(
            &(Self::ror(x, Self::ror_distance(0, 2)).bitand(&UInt64::constant(0xff00ff00ff00ff00)).unwrap())).unwrap()
    }

    #[cfg(not(feature = "compact"))]
    #[inline(always)]
    #[rustfmt::skip]
    fn rotate_rows_and_columns_1_3(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        (Self::ror(x.clone(), Self::ror_distance(1, 3)).bitand(&UInt64::constant(0x000f000f000f000f)).unwrap()).bitor(
            &(Self::ror(x, Self::ror_distance(0, 3)).bitand(&UInt64::constant(0xfff0fff0fff0fff0)).unwrap())).unwrap()
    }

    #[inline(always)]
    #[rustfmt::skip]
    fn rotate_rows_and_columns_2_2(x: UInt64<ConstraintF>) -> UInt64<ConstraintF> {
        (Self::ror(x.clone(), Self::ror_distance(2, 2)).bitand(&UInt64::constant(0x00ff00ff00ff00ff)).unwrap()).bitor(
            &(Self::ror(x, Self::ror_distance(1, 2)).bitand(&UInt64::constant(0xff00ff00ff00ff00)).unwrap())).unwrap()
    }

    define_mix_columns!(
        mix_columns_0,
        Self::rotate_rows_1,
        Self::rotate_rows_2,
        AesState<ConstraintF>,
    );

    define_mix_columns!(
        mix_columns_1,
        Self::rotate_rows_and_columns_1_1,
        Self::rotate_rows_and_columns_2_2,
        AesState<ConstraintF>,
    );

    define_mix_columns!(
        mix_columns_2,
        Self::rotate_rows_and_columns_1_2,
        Self::rotate_rows_2,
        AesState<ConstraintF>,
    );

    define_mix_columns!(
        mix_columns_3,
        Self::rotate_rows_and_columns_1_3,
        Self::rotate_rows_and_columns_2_2,
        AesState<ConstraintF>,
    );
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

    #[allow(unused_variables, unused_mut)]
    fn encrypt(
        _parameters: &Self::ParametersVar,
        message: &Self::PlaintextVar,
        _randomness: &Self::RandomnessVar,
        key: &Self::KeyVar,
    ) -> Result<Self::OutputVar, SynthesisError> {
        let rkeys: Vec<UInt64<ConstraintF>> = Aes128Gadget::aes128_key_schedule(key.key.clone());
        let mut blocks: [[UInt8<ConstraintF>; 16]; 4] = [
            message.plaintext.clone(),
            message.plaintext.clone(),
            message.plaintext.clone(),
            message.plaintext.clone(),
        ];
        Aes128Gadget::aes128_encrypt(&rkeys, &mut blocks);
        Ok(OutputVar{ ciphertext: blocks[0].clone() })
    }
}

#[cfg(test)]
#[allow(unused_imports)]
mod aes_test {
    use super::*;

    use ark_ed_on_bls12_381::{EdwardsProjective as JubJub, Fr};
    use ark_r1cs_std::R1CSVar;

    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use crate::encryption::{SymmetricEncryptionScheme};

    #[test]
    #[allow(dead_code, unused_variables)]
    fn test_basic() {
        let rng = &mut test_rng();

        type MyEnc = Aes128;
        type MyGadget = Aes128Gadget<Fr>;

        // compute primitive result
        let parameters = MyEnc::setup(rng).unwrap();
        let key = MyEnc::keygen(&parameters, rng).unwrap();
        let mut msg = [0u8; 16];
        rng.fill_bytes(&mut msg);
        let randomness = Randomness {};
        let primitive_result = MyEnc::encrypt(&parameters, &key, &msg, &randomness).unwrap();

        let cs = ConstraintSystem::<Fr>::new_ref();

        println!("key = {:?}", key);
        println!("msg = {:?}", msg);
        println!("E(msg, key) = {:?}", primitive_result);

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
            <MyGadget as SymmetricEncryptionGadget<MyEnc, Fr>>::OutputVar::new_input(
                ark_relations::ns!(cs, "gadget_expected"),
                || Ok(&primitive_result),
            )
                .unwrap();
        expected_var.enforce_equal(&result_var).unwrap();

        // TODO: this test isn't passing yet, which means that there is something wrong in the aes implementation.
        // TODO: also, ask what an acceptable clock runtime is for this process.
        assert_eq!(primitive_result, result_var.ciphertext.value().unwrap().as_slice());
        assert!(cs.is_satisfied().unwrap());
    }
}