//! Poseidon2 example using the standard BabyBear24 implementation.
//!
//! Run with: cargo run --example poseidon2_helper

use p3_baby_bear::{BabyBear, default_babybear_poseidon2_24};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

fn main() {
    println!("Poseidon2 BabyBear24 - Standard Implementation");
    println!("===============================================\n");

    // Use the default BabyBear24 Poseidon2 from p3-baby-bear
    // This uses the same round constants as Lean's BabyBear24
    let poseidon2 = default_babybear_poseidon2_24();

    // Input: [0, 1, 2, ..., 23]
    // In Lean: Array.iota 23 produces [0, 1, ..., 23] (24 elements)
    let mut state: [BabyBear; 24] = core::array::from_fn(|i| BabyBear::new(i as u32));

    println!("Input (24 elements): [0, 1, 2, ..., 23]");
    print!("  [");
    for (i, elem) in state.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("{}", elem.as_canonical_u32());
    }
    println!("]\n");

    // Apply Poseidon2 permutation
    poseidon2.permute_mut(&mut state);

    println!("Output after Poseidon2 permutation:");
    print!("  [");
    for (i, elem) in state.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("{}", elem.as_canonical_u32());
    }
    println!("]\n");

    // Also print in hex for easy comparison with Lean output
    println!("Output in hex:");
    print!("  [");
    for (i, elem) in state.iter().enumerate() {
        if i > 0 {
            print!(", ");
        }
        print!("0x{:08x}", elem.as_canonical_u32());
    }
    println!("]");

    println!("\n----------------------------------------------------");
    println!("This uses the standard p3-baby-bear Poseidon2 implementation.");
}
