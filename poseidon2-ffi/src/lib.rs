//! FFI wrapper for Poseidon2 BabyBear width-16 permutation.

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

/// Applies Poseidon2 BabyBear16 permutation over a 64-byte (16×u32 LE) buffer.
///
/// # Safety
/// - `input_ptr` must point to 64 readable bytes.
/// - `output_ptr` must point to 64 writable bytes.
///
/// # Panics
/// On null pointers or wrong lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear16_permute_bytes(
    input_ptr: *const u8,
    input_len: usize,
    output_ptr: *mut u8,
    output_len: usize,
) {
    assert!(!input_ptr.is_null(), "null input pointer");
    assert!(!output_ptr.is_null(), "null output pointer");
    assert!(input_len == 64, "input_len must be 64, got {input_len}");
    assert!(output_len == 64, "output_len must be 64, got {output_len}");

    let input = unsafe { core::slice::from_raw_parts(input_ptr, 64) };
    let output = unsafe { core::slice::from_raw_parts_mut(output_ptr, 64) };

    let mut state: [BabyBear; 16] = core::array::from_fn(|i| {
        BabyBear::new(u32::from_le_bytes(input[i * 4..][..4].try_into().unwrap()))
    });

    default_babybear_poseidon2_16().permute_mut(&mut state);

    for (i, elem) in state.iter().enumerate() {
        output[i * 4..][..4].copy_from_slice(&elem.as_canonical_u32().to_le_bytes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permute_bytes() {
        let input: Vec<u8> = (0u32..16).flat_map(|x| x.to_le_bytes()).collect();
        let mut output = [0u8; 64];

        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 64, output.as_mut_ptr(), 64);
        }

        let mut expected: [BabyBear; 16] = core::array::from_fn(|i| BabyBear::new(i as u32));
        default_babybear_poseidon2_16().permute_mut(&mut expected);

        for (i, elem) in expected.iter().enumerate() {
            let got = u32::from_le_bytes(output[i * 4..][..4].try_into().unwrap());
            assert_eq!(got, elem.as_canonical_u32(), "mismatch at index {i}");
        }
    }

    #[test]
    #[should_panic(expected = "null input")]
    fn test_null_input() {
        let mut output = [0u8; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(core::ptr::null(), 64, output.as_mut_ptr(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "null output")]
    fn test_null_output() {
        let input = [0u8; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 64, core::ptr::null_mut(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "input_len must be 64")]
    fn test_wrong_input_len() {
        let input = [0u8; 64];
        let mut output = [0u8; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 32, output.as_mut_ptr(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "output_len must be 64")]
    fn test_wrong_output_len() {
        let input = [0u8; 64];
        let mut output = [0u8; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 64, output.as_mut_ptr(), 32);
        }
    }
}
