//! Poseidon2 example using the standard BabyBear implementations.
//!
//! Run with: cargo run --example poseidon2_helper

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_16, default_babybear_poseidon2_24};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

fn print_state<const N: usize>(state: &[BabyBear; N]) {
    print!("  [");
    for (i, elem) in state.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("{}", elem.as_canonical_u32());
    }
    println!("]");
}

fn print_state_hex<const N: usize>(state: &[BabyBear; N]) {
    print!("  [");
    for (i, elem) in state.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("0x{:08x}", elem.as_canonical_u32());
    }
    println!("]");
}

fn main() {
    println!("Poseidon2 BabyBear - Standard Implementation");
    println!("=============================================\n");

    // =========================================================================
    // Width 16
    // =========================================================================
    println!("=== Width 16 (BabyBear16) ===\n");

    let poseidon2_16 = default_babybear_poseidon2_16();
    let mut state16: [BabyBear; 16] = core::array::from_fn(|i| BabyBear::new(i as u32));

    println!("Input (16 elements): [0, 1, 2, ..., 15]");
    print_state(&state16);
    println!();

    poseidon2_16.permute_mut(&mut state16);

    println!("Output after Poseidon2 permutation:");
    print_state(&state16);
    println!();

    println!("Output in hex:");
    print_state_hex(&state16);
    println!();

    // =========================================================================
    // Width 24
    // =========================================================================
    println!("=== Width 24 (BabyBear24) ===\n");

    let poseidon2_24 = default_babybear_poseidon2_24();
    let mut state24: [BabyBear; 24] = core::array::from_fn(|i| BabyBear::new(i as u32));

    println!("Input (24 elements): [0, 1, 2, ..., 23]");
    print_state(&state24);
    println!();

    poseidon2_24.permute_mut(&mut state24);

    println!("Output after Poseidon2 permutation:");
    print_state(&state24);
    println!();

    println!("Output in hex:");
    print_state_hex(&state24);

    println!("\n----------------------------------------------------");
    println!("This uses the standard p3-baby-bear Poseidon2 implementation.");
}
