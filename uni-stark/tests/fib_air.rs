use core::borrow::Borrow;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PermutationAirBuilder};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::{DuplexChallenger, HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{HidingFriPcs, TwoAdicFriPcs, create_test_fri_config};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs};
use p3_symmetric::{
    CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher, TruncatedPermutation,
};
use p3_uni_stark::{prove, verify, DebugConstraintBuilder, StarkConfig};
use rand::SeedableRng;
use rand::rngs::SmallRng;

const NUM_FIBONACCI_COLS: usize = 3;

/// For testing modularity

pub trait MultiTableAirBuilder<'sum>: PermutationAirBuilder {
    type LogUpSum: Into<Self::ExprEF> + Copy;

    fn cumulative_sum(&self) -> &'sum Self::LogUpSum;
}










pub struct AddGadget {}

impl<F> BaseAir<F> for AddGadget {
    fn width(&self) -> usize {
        NUM_FIBONACCI_COLS
    }
}

pub struct FibonacciAir {}

impl<F> BaseAir<F> for FibonacciAir {
    fn width(&self) -> usize {
        NUM_FIBONACCI_COLS
    }
}

impl<Builder: PermutationAirBuilder> Air<Builder> for AddGadget {
    fn eval(&self, builder: &mut Builder) {
        let main = builder.main();

        let local = main
            .row_slice(0)
            .expect("Matrix is empty?");

        let local_left = (*local)[0];
        let local_right = (*local)[1];
        let local_sum = (*local)[2];
        
        builder.assert_eq(local_left + local_right, local_sum);
    }
}

impl<'a, F> Air<DebugConstraintBuilder<'a, F>> for AddGadget {
    fn eval(&self, builder: &mut Builder) {
        let main = builder.main();

        let local = main
            .row_slice(0)
            .expect("Matrix is empty?");

        let local_left = (*local)[0];
        let local_right = (*local)[1];
        let local_sum = (*local)[2];
        
        builder.assert_eq(local_left + local_right, local_sum);
    }
}

impl<Builder: AirBuilderWithPublicValues> Air<Builder> for FibonacciAir {
    fn eval(&self, builder: &mut Builder) {
        let main = builder.main();

        let pis = builder.public_values();

        let a = pis[0];
        let b = pis[1];
        let x = pis[2];

        let (local, next) = (
            main.row_slice(0).expect("Matrix is empty?"),
            main.row_slice(1).expect("Matrix only has 1 row?"),
        );

        let local_left = (*local)[0];
        let local_right = (*local)[1];
        let local_sum = (*local)[2];
        
        let next_left = (*next)[0];
        let next_right = (*next)[1];
        
        // Link one row to the next
        builder.when_transition().assert_eq(next_left, local_right);
        builder.when_transition().assert_eq(next_right, local_sum);

        // Connect the public inputs
        builder.when_first_row().assert_eq(local_left, a);
        builder.when_first_row().assert_eq(local_right, b);
        builder.when_last_row().assert_eq(local_sum, x);
    }
}

pub fn generate_trace_rows<F: PrimeField64>(a: u64, b: u64, n: usize) -> RowMajorMatrix<F> {
    assert!(n.is_power_of_two());

    let mut trace = RowMajorMatrix::new(
        F::zero_vec(n * NUM_FIBONACCI_COLS),
        NUM_FIBONACCI_COLS
    );

    let a_f = F::from_u64(a);
    let b_f = F::from_u64(b);
    trace.row_mut(0)[0] = a_f;
    trace.row_mut(0)[1] = b_f;
    if a == 0 {
        trace.row_mut(0)[2] = a_f + b_f;
    } else {
        trace.row_mut(0)[2] = a_f + b_f;
    }

    for i in 1..n {
        let a_f = (*trace.row_slice(i-1).unwrap())[1];
        trace.row_mut(i)[0] = a_f;
        let b_f = (*trace.row_slice(i-1).unwrap())[2];
        trace.row_mut(i)[1] = b_f;
        trace.row_mut(i)[2] = a_f + b_f;
    }

    trace
}

type Val = BabyBear;
type Perm = Poseidon2BabyBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
type Challenge = BinomialExtensionField<Val, 4>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Dft = Radix2DitParallel<Val>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

/// n-th Fibonacci number expected to be x
fn test_public_value_impl(n: usize, x: u64, log_final_poly_len: usize) {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fib_trace = generate_trace_rows::<Val>(0, 1, n);
    let add_trace = generate_trace_rows::<Val>(1, 1, n);
    let fri_config = create_test_fri_config(challenge_mmcs, log_final_poly_len);
    let pcs = Pcs::new(dft, val_mmcs, fri_config);
    let challenger = Challenger::new(perm);

    let config = MyConfig::new(pcs, challenger);
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(x)];

    let proof = prove(&config, &FibonacciAir {}, fib_trace, &pis);
    verify(&config, &FibonacciAir {}, &proof, &pis).expect("FibonacciAir verification failed");

    let proof = prove(&config, &AddGadget {}, add_trace, &pis);
    verify(&config, &AddGadget {}, &proof, &pis).expect("AddGadget verification failed");

    assert!(false);
}

#[test]
fn test_zk() {
    type ByteHash = Keccak256Hash;
    let byte_hash = ByteHash {};

    type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
    let u64_hash = U64Hash::new(KeccakF {});

    type FieldHash = SerializingHasher<U64Hash>;
    let field_hash = FieldHash::new(u64_hash);

    type MyCompress = CompressionFunctionFromHasher<U64Hash, 2, 4>;
    let compress = MyCompress::new(u64_hash);

    type ValHidingMmcs = MerkleTreeHidingMmcs<
        [Val; p3_keccak::VECTOR_LEN],
        [u64; p3_keccak::VECTOR_LEN],
        FieldHash,
        MyCompress,
        SmallRng,
        4,
        4,
    >;

    let rng = SmallRng::seed_from_u64(1);
    let val_mmcs = ValHidingMmcs::new(field_hash, compress, rng);

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

    type ChallengeHidingMmcs = ExtensionMmcs<Val, Challenge, ValHidingMmcs>;

    let n = 1 << 3;
    let x = 21;

    let challenge_mmcs = ChallengeHidingMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let trace = generate_trace_rows::<Val>(0, 1, n);
    let fri_config = create_test_fri_config(challenge_mmcs, 2);
    type HidingPcs = HidingFriPcs<Val, Dft, ValHidingMmcs, ChallengeHidingMmcs, SmallRng>;
    type MyHidingConfig = StarkConfig<HidingPcs, Challenge, Challenger>;
    let pcs = HidingPcs::new(dft, val_mmcs, fri_config, 4, SmallRng::seed_from_u64(1));
    let challenger = Challenger::from_hasher(vec![], byte_hash);
    let config = MyHidingConfig::new(pcs, challenger);
    let pis = vec![BabyBear::ZERO, BabyBear::ONE, BabyBear::from_u64(x)];
    let proof = prove(&config, &FibonacciAir {}, trace, &pis);
    verify(&config, &FibonacciAir {}, &proof, &pis).expect("verification failed");
}

#[test]
fn test_one_row_trace() {
    // Need to set log_final_poly_len to ensure log_min_height > config.log_final_poly_len + config.log_blowup
    test_public_value_impl(1, 1, 0);
}

#[test]
fn test_public_value() {
    test_public_value_impl(1 << 3, 21, 2);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "assertion `left == right` failed: constraints had nonzero value")]
fn test_incorrect_public_value() {
    let mut rng = SmallRng::seed_from_u64(1);
    let perm = Perm::new_from_rng_128(&mut rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let dft = Dft::default();
    let fri_config = create_test_fri_config(challenge_mmcs, 1);
    let trace = generate_trace_rows::<Val>(0, 1, 1 << 3);
    let pcs = Pcs::new(dft, val_mmcs, fri_config);
    let challenger = Challenger::new(perm);
    let config = MyConfig::new(pcs, challenger);
    let pis = vec![
        BabyBear::ZERO,
        BabyBear::ONE,
        BabyBear::from_u32(123_123), // incorrect result
    ];
    prove(&config, &FibonacciAir {}, trace, &pis);
}
