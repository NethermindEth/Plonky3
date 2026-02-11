/* C shim: Lean4 FFI → Poseidon2 Rust (BabyBear, width 16) */

#include <lean/lean.h>
#include <stdint.h>

extern void lean_poseidon2_babybear16_permute_bytes(const uint8_t*, size_t, uint8_t*, size_t);

LEAN_EXPORT lean_obj_res lean_poseidon2_babybear16_permute_wrapper(b_lean_obj_arg input) {
    if (lean_sarray_size(input) != 64)
        return lean_alloc_sarray(1, 0, 0);
    lean_obj_res out = lean_alloc_sarray(1, 64, 64);
    lean_poseidon2_babybear16_permute_bytes(lean_sarray_cptr(input), 64, lean_sarray_cptr(out), 64);
    return out;
}
