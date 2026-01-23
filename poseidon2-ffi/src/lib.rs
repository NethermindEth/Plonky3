//! FFI wrapper for Poseidon2 BabyBear24 permutation.
//!
//! This crate provides C-compatible functions that can be called from Lean4
//! via FFI to compute Poseidon2 hashes using the Plonky3 implementation.

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_24};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

/// Applies the Poseidon2 BabyBear24 permutation to the input state.
///
/// # Safety
///
/// - `input` must be a valid pointer to an array of 24 `u32` values
/// - `output` must be a valid pointer to an array of 24 `u32` values with write access
/// - The caller is responsible for ensuring the pointers are valid and properly aligned
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear24_permute(
    input: *const u32,
    output: *mut u32,
) {
    // Create the Poseidon2 permutation instance
    let poseidon2 = default_babybear_poseidon2_24();

    // Read input into BabyBear array
    let mut state: [BabyBear; 24] = core::array::from_fn(|i| {
        // SAFETY: Caller guarantees input points to 24 valid u32 values
        let val = unsafe { *input.add(i) };
        BabyBear::new(val)
    });

    // Apply the permutation
    poseidon2.permute_mut(&mut state);

    // Write output
    for (i, elem) in state.iter().enumerate() {
        // SAFETY: Caller guarantees output points to 24 writable u32 values
        unsafe {
            *output.add(i) = elem.as_canonical_u32();
        }
    }
}

/// Wrapper function for Lean FFI that works with byte arrays.
///
/// This function takes a pointer to input bytes (96 bytes = 24 × 4 bytes for u32 values)
/// and writes the result to the output pointer.
///
/// # Safety
///
/// - `input_ptr` must point to at least 96 bytes of readable memory
/// - `output_ptr` must point to at least 96 bytes of writable memory
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear24_permute_bytes(
    input_ptr: *const u8,
    output_ptr: *mut u8,
) {
    let poseidon2 = default_babybear_poseidon2_24();

    // Read input bytes as little-endian u32 values
    let mut state: [BabyBear; 24] = core::array::from_fn(|i| {
        let offset = i * 4;
        let bytes: [u8; 4] = unsafe {
            [
                *input_ptr.add(offset),
                *input_ptr.add(offset + 1),
                *input_ptr.add(offset + 2),
                *input_ptr.add(offset + 3),
            ]
        };
        let val = u32::from_le_bytes(bytes);
        BabyBear::new(val)
    });

    // Apply the permutation
    poseidon2.permute_mut(&mut state);

    // Write output as little-endian bytes
    for (i, elem) in state.iter().enumerate() {
        let val = elem.as_canonical_u32();
        let bytes = val.to_le_bytes();
        let offset = i * 4;
        unsafe {
            *output_ptr.add(offset) = bytes[0];
            *output_ptr.add(offset + 1) = bytes[1];
            *output_ptr.add(offset + 2) = bytes[2];
            *output_ptr.add(offset + 3) = bytes[3];
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ffi_permutation() {
        // Input: [0, 1, 2, ..., 23]
        let input: [u32; 24] = core::array::from_fn(|i| i as u32);
        let mut output: [u32; 24] = [0; 24];

        unsafe {
            lean_poseidon2_babybear24_permute(input.as_ptr(), output.as_mut_ptr());
        }

        // Verify against direct Rust computation
        let poseidon2 = default_babybear_poseidon2_24();
        let mut expected: [BabyBear; 24] = core::array::from_fn(|i| BabyBear::new(i as u32));
        poseidon2.permute_mut(&mut expected);

        for (i, elem) in expected.iter().enumerate() {
            assert_eq!(output[i], elem.as_canonical_u32(), "Mismatch at index {}", i);
        }
    }
}
