/*
 * C shim for Lean4 FFI to Poseidon2 Rust implementation.
 *
 * This file provides the bridge between Lean's object system and
 * the C-compatible Rust functions for multiple widths (16, 24).
 */

#include <lean/lean.h>
#include <stdint.h>

/* Forward declarations of the Rust functions (with length parameters) */
extern void lean_poseidon2_babybear16_permute_bytes(
    const uint8_t* input_ptr,
    size_t input_len,
    uint8_t* output_ptr,
    size_t output_len
);

extern void lean_poseidon2_babybear24_permute_bytes(
    const uint8_t* input_ptr,
    size_t input_len,
    uint8_t* output_ptr,
    size_t output_len
);

/*
 * Lean FFI wrapper for Poseidon2 BabyBear16 permutation.
 *
 * Takes a ByteArray of 64 bytes (16 × 4-byte little-endian u32 values)
 * and returns a new ByteArray of 64 bytes with the permuted state.
 *
 * Lean signature: @[extern "lean_poseidon2_babybear16_permute_wrapper"]
 *                 opaque poseidon2Permute16Raw : @& ByteArray → ByteArray
 */
LEAN_EXPORT lean_obj_res lean_poseidon2_babybear16_permute_wrapper(b_lean_obj_arg input) {
    /* Get the size of the input ByteArray */
    size_t input_size = lean_sarray_size(input);
    
    /* Validate input size (should be 64 bytes = 16 * 4) */
    if (input_size != 64) {
        /* Return empty ByteArray on invalid input */
        return lean_alloc_sarray(1, 0, 0);
    }
    
    /* Get pointer to input data */
    const uint8_t* input_ptr = lean_sarray_cptr(input);
    
    /* Allocate output ByteArray */
    lean_obj_res output = lean_alloc_sarray(1, 64, 64);
    uint8_t* output_ptr = lean_sarray_cptr(output);
    
    /* Call the Rust permutation function with explicit lengths */
    lean_poseidon2_babybear16_permute_bytes(input_ptr, input_size, output_ptr, 64);
    
    return output;
}

/*
 * Lean FFI wrapper for Poseidon2 BabyBear24 permutation.
 *
 * Takes a ByteArray of 96 bytes (24 × 4-byte little-endian u32 values)
 * and returns a new ByteArray of 96 bytes with the permuted state.
 *
 * Lean signature: @[extern "lean_poseidon2_babybear24_permute_wrapper"]
 *                 opaque poseidon2Permute24Raw : @& ByteArray → ByteArray
 */
LEAN_EXPORT lean_obj_res lean_poseidon2_babybear24_permute_wrapper(b_lean_obj_arg input) {
    /* Get the size of the input ByteArray */
    size_t input_size = lean_sarray_size(input);
    
    /* Validate input size (should be 96 bytes = 24 * 4) */
    if (input_size != 96) {
        /* Return empty ByteArray on invalid input */
        return lean_alloc_sarray(1, 0, 0);
    }
    
    /* Get pointer to input data */
    const uint8_t* input_ptr = lean_sarray_cptr(input);
    
    /* Allocate output ByteArray */
    lean_obj_res output = lean_alloc_sarray(1, 96, 96);
    uint8_t* output_ptr = lean_sarray_cptr(output);
    
    /* Call the Rust permutation function with explicit lengths */
    lean_poseidon2_babybear24_permute_bytes(input_ptr, input_size, output_ptr, 96);
    
    return output;
}
