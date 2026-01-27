//! FFI wrapper for Poseidon2 BabyBear permutations.
//!
//! This crate provides C-compatible functions that can be called from Lean4
//! via FFI to compute Poseidon2 hashes using the Plonky3 implementation.
//!
//! Supported widths:
//! - 16 elements (64 bytes)
//! - 24 elements (96 bytes)

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16, default_babybear_poseidon2_24};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

// =============================================================================
// Safety check helpers
// =============================================================================

/// Panics if the pointer is null.
#[inline]
fn assert_not_null<T>(ptr: *const T, name: &str) {
    assert!(!ptr.is_null(), "FFI safety violation: {name} pointer is null");
}

/// Panics if the pointer is null (mutable version).
#[inline]
fn assert_not_null_mut<T>(ptr: *mut T, name: &str) {
    assert!(!ptr.is_null(), "FFI safety violation: {name} pointer is null");
}

/// Panics if the pointer is not properly aligned for type T.
#[inline]
fn assert_aligned<T>(ptr: *const T, name: &str) {
    let align = core::mem::align_of::<T>();
    assert!(
        (ptr as usize) % align == 0,
        "FFI safety violation: {name} pointer is not aligned (required: {align}-byte alignment, got address: {:p})",
        ptr
    );
}

/// Panics if the mutable pointer is not properly aligned for type T.
#[inline]
fn assert_aligned_mut<T>(ptr: *mut T, name: &str) {
    let align = core::mem::align_of::<T>();
    assert!(
        (ptr as usize) % align == 0,
        "FFI safety violation: {name} pointer is not aligned (required: {align}-byte alignment, got address: {:p})",
        ptr
    );
}

/// Panics if the length doesn't match the expected value.
#[inline]
fn assert_length(actual: usize, expected: usize, context: &str) {
    assert!(
        actual == expected,
        "FFI safety violation: {context} length mismatch (expected {expected}, got {actual})"
    );
}

// =============================================================================
// Width 16 (64 bytes)
// =============================================================================

/// Applies the Poseidon2 BabyBear16 permutation to the input state.
///
/// # Panics
///
/// This function will panic if:
/// - `input` is null
/// - `output` is null
/// - `input` is not 4-byte aligned
/// - `output` is not 4-byte aligned
/// - `input_len` is not exactly 16
/// - `output_len` is not exactly 16
///
/// # Safety
///
/// - `input` must point to at least 16 valid `u32` values
/// - `output` must point to at least 16 `u32` values with write access
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear16_permute(
    input: *const u32,
    input_len: usize,
    output: *mut u32,
    output_len: usize,
) {
    // Runtime safety checks
    assert_not_null(input, "input");
    assert_not_null_mut(output, "output");
    assert_aligned(input, "input");
    assert_aligned_mut(output, "output");
    assert_length(input_len, 16, "input");
    assert_length(output_len, 16, "output");

    let poseidon2 = default_babybear_poseidon2_16();
    
    let mut state: [BabyBear; 16] = core::array::from_fn(|i| {
        let val = unsafe { *input.add(i) };
        BabyBear::new(val)
    });
    
    poseidon2.permute_mut(&mut state);
    
    for (i, elem) in state.iter().enumerate() {
        unsafe {
            *output.add(i) = elem.as_canonical_u32();
        }
    }
}

/// Wrapper function for Lean FFI that works with byte arrays (width 16).
///
/// # Panics
///
/// This function will panic if:
/// - `input_ptr` is null
/// - `output_ptr` is null
/// - `input_len` is not exactly 64
/// - `output_len` is not exactly 64
///
/// # Safety
///
/// - `input_ptr` must point to at least 64 bytes of readable memory
/// - `output_ptr` must point to at least 64 bytes of writable memory
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear16_permute_bytes(
    input_ptr: *const u8,
    input_len: usize,
    output_ptr: *mut u8,
    output_len: usize,
) {
    // Runtime safety checks
    assert_not_null(input_ptr, "input_ptr");
    assert_not_null_mut(output_ptr, "output_ptr");
    assert_length(input_len, 64, "input");
    assert_length(output_len, 64, "output");

    let poseidon2 = default_babybear_poseidon2_16();

    let mut state: [BabyBear; 16] = core::array::from_fn(|i| {
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

    poseidon2.permute_mut(&mut state);

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

// =============================================================================
// Width 24 (96 bytes)
// =============================================================================

/// Applies the Poseidon2 BabyBear24 permutation to the input state.
///
/// # Panics
///
/// This function will panic if:
/// - `input` is null
/// - `output` is null
/// - `input` is not 4-byte aligned
/// - `output` is not 4-byte aligned
/// - `input_len` is not exactly 24
/// - `output_len` is not exactly 24
///
/// # Safety
///
/// - `input` must point to at least 24 valid `u32` values
/// - `output` must point to at least 24 `u32` values with write access
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear24_permute(
    input: *const u32,
    input_len: usize,
    output: *mut u32,
    output_len: usize,
) {
    // Runtime safety checks
    assert_not_null(input, "input");
    assert_not_null_mut(output, "output");
    assert_aligned(input, "input");
    assert_aligned_mut(output, "output");
    assert_length(input_len, 24, "input");
    assert_length(output_len, 24, "output");

    let poseidon2 = default_babybear_poseidon2_24();

    let mut state: [BabyBear; 24] = core::array::from_fn(|i| {
        let val = unsafe { *input.add(i) };
        BabyBear::new(val)
    });

    poseidon2.permute_mut(&mut state);

    for (i, elem) in state.iter().enumerate() {
        unsafe {
            *output.add(i) = elem.as_canonical_u32();
        }
    }
}

/// Wrapper function for Lean FFI that works with byte arrays (width 24).
///
/// # Panics
///
/// This function will panic if:
/// - `input_ptr` is null
/// - `output_ptr` is null
/// - `input_len` is not exactly 96
/// - `output_len` is not exactly 96
///
/// # Safety
///
/// - `input_ptr` must point to at least 96 bytes of readable memory
/// - `output_ptr` must point to at least 96 bytes of writable memory
#[unsafe(no_mangle)]
pub unsafe extern "C" fn lean_poseidon2_babybear24_permute_bytes(
    input_ptr: *const u8,
    input_len: usize,
    output_ptr: *mut u8,
    output_len: usize,
) {
    // Runtime safety checks
    assert_not_null(input_ptr, "input_ptr");
    assert_not_null_mut(output_ptr, "output_ptr");
    assert_length(input_len, 96, "input");
    assert_length(output_len, 96, "output");

    let poseidon2 = default_babybear_poseidon2_24();

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

    poseidon2.permute_mut(&mut state);

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
    fn test_ffi_permutation_16() {
        let input: [u32; 16] = core::array::from_fn(|i| i as u32);
        let mut output: [u32; 16] = [0; 16];

        unsafe {
            lean_poseidon2_babybear16_permute(input.as_ptr(), 16, output.as_mut_ptr(), 16);
        }

        let poseidon2 = default_babybear_poseidon2_16();
        let mut expected: [BabyBear; 16] = core::array::from_fn(|i| BabyBear::new(i as u32));
        poseidon2.permute_mut(&mut expected);

        for (i, elem) in expected.iter().enumerate() {
            assert_eq!(output[i], elem.as_canonical_u32(), "Mismatch at index {}", i);
        }
    }

    #[test]
    fn test_ffi_permutation_24() {
        let input: [u32; 24] = core::array::from_fn(|i| i as u32);
        let mut output: [u32; 24] = [0; 24];

        unsafe {
            lean_poseidon2_babybear24_permute(input.as_ptr(), 24, output.as_mut_ptr(), 24);
        }

        let poseidon2 = default_babybear_poseidon2_24();
        let mut expected: [BabyBear; 24] = core::array::from_fn(|i| BabyBear::new(i as u32));
        poseidon2.permute_mut(&mut expected);

        for (i, elem) in expected.iter().enumerate() {
            assert_eq!(output[i], elem.as_canonical_u32(), "Mismatch at index {}", i);
        }
    }

    #[test]
    fn test_ffi_bytes_16() {
        let input: [u32; 16] = core::array::from_fn(|i| i as u32);
        let input_bytes: Vec<u8> = input.iter().flat_map(|x| x.to_le_bytes()).collect();
        let mut output_bytes: [u8; 64] = [0; 64];

        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input_bytes.as_ptr(), 64, output_bytes.as_mut_ptr(), 64);
        }

        let mut output_u32: [u32; 16] = [0; 16];
        unsafe {
            lean_poseidon2_babybear16_permute(input.as_ptr(), 16, output_u32.as_mut_ptr(), 16);
        }

        for i in 0..16 {
            let bytes_val = u32::from_le_bytes([
                output_bytes[i * 4],
                output_bytes[i * 4 + 1],
                output_bytes[i * 4 + 2],
                output_bytes[i * 4 + 3],
            ]);
            assert_eq!(bytes_val, output_u32[i], "Byte/u32 mismatch at index {}", i);
        }
    }

    #[test]
    fn test_ffi_bytes_24() {
        let input: [u32; 24] = core::array::from_fn(|i| i as u32);
        let input_bytes: Vec<u8> = input.iter().flat_map(|x| x.to_le_bytes()).collect();
        let mut output_bytes: [u8; 96] = [0; 96];

        unsafe {
            lean_poseidon2_babybear24_permute_bytes(input_bytes.as_ptr(), 96, output_bytes.as_mut_ptr(), 96);
        }

        let mut output_u32: [u32; 24] = [0; 24];
        unsafe {
            lean_poseidon2_babybear24_permute(input.as_ptr(), 24, output_u32.as_mut_ptr(), 24);
        }

        for i in 0..24 {
            let bytes_val = u32::from_le_bytes([
                output_bytes[i * 4],
                output_bytes[i * 4 + 1],
                output_bytes[i * 4 + 2],
                output_bytes[i * 4 + 3],
            ]);
            assert_eq!(bytes_val, output_u32[i], "Byte/u32 mismatch at index {}", i);
        }
    }

    // Null pointer tests
    #[test]
    #[should_panic(expected = "input pointer is null")]
    fn test_null_input_16() {
        let mut output: [u32; 16] = [0; 16];
        unsafe {
            lean_poseidon2_babybear16_permute(core::ptr::null(), 16, output.as_mut_ptr(), 16);
        }
    }

    #[test]
    #[should_panic(expected = "output pointer is null")]
    fn test_null_output_16() {
        let input: [u32; 16] = [0; 16];
        unsafe {
            lean_poseidon2_babybear16_permute(input.as_ptr(), 16, core::ptr::null_mut(), 16);
        }
    }

    #[test]
    #[should_panic(expected = "input_ptr pointer is null")]
    fn test_null_input_bytes_16() {
        let mut output: [u8; 64] = [0; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(core::ptr::null(), 64, output.as_mut_ptr(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "output_ptr pointer is null")]
    fn test_null_output_bytes_16() {
        let input: [u8; 64] = [0; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 64, core::ptr::null_mut(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "input pointer is null")]
    fn test_null_input_24() {
        let mut output: [u32; 24] = [0; 24];
        unsafe {
            lean_poseidon2_babybear24_permute(core::ptr::null(), 24, output.as_mut_ptr(), 24);
        }
    }

    #[test]
    #[should_panic(expected = "output pointer is null")]
    fn test_null_output_24() {
        let input: [u32; 24] = [0; 24];
        unsafe {
            lean_poseidon2_babybear24_permute(input.as_ptr(), 24, core::ptr::null_mut(), 24);
        }
    }

    // Length mismatch tests
    #[test]
    #[should_panic(expected = "input length mismatch (expected 16, got 8)")]
    fn test_wrong_input_len_16() {
        let input: [u32; 16] = [0; 16];
        let mut output: [u32; 16] = [0; 16];
        unsafe {
            lean_poseidon2_babybear16_permute(input.as_ptr(), 8, output.as_mut_ptr(), 16);
        }
    }

    #[test]
    #[should_panic(expected = "output length mismatch (expected 16, got 24)")]
    fn test_wrong_output_len_16() {
        let input: [u32; 16] = [0; 16];
        let mut output: [u32; 16] = [0; 16];
        unsafe {
            lean_poseidon2_babybear16_permute(input.as_ptr(), 16, output.as_mut_ptr(), 24);
        }
    }

    #[test]
    #[should_panic(expected = "input length mismatch (expected 64, got 32)")]
    fn test_wrong_input_len_bytes_16() {
        let input: [u8; 64] = [0; 64];
        let mut output: [u8; 64] = [0; 64];
        unsafe {
            lean_poseidon2_babybear16_permute_bytes(input.as_ptr(), 32, output.as_mut_ptr(), 64);
        }
    }

    #[test]
    #[should_panic(expected = "input length mismatch (expected 24, got 16)")]
    fn test_wrong_input_len_24() {
        let input: [u32; 24] = [0; 24];
        let mut output: [u32; 24] = [0; 24];
        unsafe {
            lean_poseidon2_babybear24_permute(input.as_ptr(), 16, output.as_mut_ptr(), 24);
        }
    }

    #[test]
    #[should_panic(expected = "input length mismatch (expected 96, got 64)")]
    fn test_wrong_input_len_bytes_24() {
        let input: [u8; 96] = [0; 96];
        let mut output: [u8; 96] = [0; 96];
        unsafe {
            lean_poseidon2_babybear24_permute_bytes(input.as_ptr(), 64, output.as_mut_ptr(), 96);
        }
    }
}
