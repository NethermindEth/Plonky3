use alloc::vec::Vec;

use p3_air::logup::LogupInteractionAirBuilder;
use p3_air::{
    Air, AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, PermutationAirBuilder,
};
use p3_field::{ExtensionField, Field};
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use tracing::instrument;

/// Runs constraint checks using a given AIR definition and trace matrix.
///
/// Iterates over every row in `main`, providing both the current and next row
/// (with wraparound) to the AIR logic. Also injects public values into the builder
/// for first/last row assertions.
///
/// # Arguments
/// - `air`: The AIR logic to run
/// - `main`: The trace matrix (rows of witness values)
/// - `public_values`: Public values provided to the builder
#[instrument(name = "check multitable constraints", skip_all)]
pub(crate) fn check_multitable_constraints<F, ExtF, A>(
    air: &A,
    main: &RowMajorMatrix<F>,
    permutation_trace: &RowMajorMatrix<ExtF>,
    public_values: &Vec<F>,
) where
    F: Field,
    ExtF: ExtensionField<F>,
    A: for<'a> Air<LogupInteractionAirBuilder<'a, DebugConstraintBuilder<'a, F, ExtF>>>,
{
    let challenges = [ExtF::from_u8(5), ExtF::from_u8(10), ExtF::from_u8(15)];

    let height = main.height();

    (0..height).for_each(|i| {
        println!("Evaluating row {i}");
        let i_next = (i + 1) % height;

        let local = main.row_slice(i).unwrap(); // i < height so unwrap should never fail.
        let next = main.row_slice(i_next).unwrap(); // i_next < height so unwrap should never fail.
        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(&*local),
            RowMajorMatrixView::new_row(&*next),
        );
        println!("Main: {main:?}");

        let local = permutation_trace.row_slice(i).unwrap(); // i < height so unwrap should never fail.
        let next = permutation_trace.row_slice(i_next).unwrap();
        let permutation_trace = VerticalPair::new(
            RowMajorMatrixView::new_row(&*local),
            RowMajorMatrixView::new_row(&*next),
        );
        println!("Permutation_trace: {permutation_trace:?}");

        let mut builder = DebugConstraintBuilder {
            row_index: i,
            main,
            permutation_trace,
            permutation_randomness: &challenges,
            public_values,
            is_first_row: F::from_bool(i == 0),
            is_last_row: F::from_bool(i == height - 1),
            is_transition: F::from_bool(i != height - 1),
        };

        let mut builder = LogupInteractionAirBuilder::new(&mut builder);

        air.eval(&mut builder);

        println!("Row {i} succeeded");
    });
}

pub(crate) fn check_cumulative_sum<F, ExtF>(permutation_traces: &[RowMajorMatrix<ExtF>])
where
    F: Field,
    ExtF: ExtensionField<F>,
{
    let sum: ExtF = permutation_traces
        .iter()
        .map(|trace| {
            let height = trace.height();

            for i in 0..height {
                let local = trace.row_slice(i).unwrap();
                let next = trace.row_slice((i + 1) % height).unwrap();
                let permutation_trace = VerticalPair::new(
                    RowMajorMatrixView::new_row(&*local),
                    RowMajorMatrixView::new_row(&*next),
                );

                let width = permutation_trace.width();
                assert_eq!(
                    permutation_trace.get(i, width - 1),
                    permutation_trace.get((i + 1) % height, width - 1)
                )
            }

            trace.get(0, trace.width() - 1).unwrap()
        })
        .sum();

    assert_eq!(sum, ExtF::ZERO);
}

/// A builder that runs constraint assertions during testing.
///
/// Used in conjunction with [`check_multitable_constraints`] to simulate
/// an execution trace and verify that the AIR logic enforces all constraints.
#[derive(Debug)]
pub struct DebugConstraintBuilder<'a, F: Field, ExtF: ExtensionField<F>> {
    /// The index of the row currently being evaluated.
    row_index: usize,
    /// A view of the current and next row as a vertical pair.
    main: VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>,

    permutation_randomness: &'a [ExtF],

    permutation_trace: VerticalPair<RowMajorMatrixView<'a, ExtF>, RowMajorMatrixView<'a, ExtF>>,
    /// The public values provided for constraint validation (e.g. inputs or outputs).
    public_values: &'a [F],
    /// A flag indicating whether this is the first row.
    is_first_row: F,
    /// A flag indicating whether this is the last row.
    is_last_row: F,
    /// A flag indicating whether this is a transition row (not the last row).
    is_transition: F,
}

impl<'a, F, ExtF> AirBuilder for DebugConstraintBuilder<'a, F, ExtF>
where
    F: Field,
    ExtF: ExtensionField<F>,
{
    type F = F;
    type Expr = F;
    type Var = F;
    type M = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;

    fn main(&self) -> Self::M {
        self.main
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    /// # Panics
    /// This function panics if `size` is not `2`.
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            self.is_transition
        } else {
            panic!("only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        assert_eq!(
            x.into(),
            F::ZERO,
            "constraints had nonzero value on row {}",
            self.row_index
        );
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        let x = x.into();
        let y = y.into();
        assert_eq!(
            x, y,
            "values didn't match on row {}: {} != {}",
            self.row_index, x, y
        );
    }
}

impl<F: Field, ExtF: ExtensionField<F>> AirBuilderWithPublicValues
    for DebugConstraintBuilder<'_, F, ExtF>
{
    type PublicVar = Self::F;

    fn public_values(&self) -> &[Self::F] {
        self.public_values
    }
}

impl<F: Field, ExtF: ExtensionField<F>> ExtensionBuilder for DebugConstraintBuilder<'_, F, ExtF> {
    type EF = ExtF;

    type ExprEF = ExtF;

    type VarEF = ExtF;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        assert_eq!(x.into(), ExtF::ZERO)
    }
}

impl<'a, F: Field, ExtF: ExtensionField<F>> PermutationAirBuilder
    for DebugConstraintBuilder<'a, F, ExtF>
{
    type MP = VerticalPair<RowMajorMatrixView<'a, ExtF>, RowMajorMatrixView<'a, ExtF>>;

    type RandomVar = ExtF;

    fn permutation(&self) -> Self::MP {
        self.permutation_trace
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        self.permutation_randomness
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_air::{BaseAir, BaseAirWithPublicValues, InteractionAirBuilder};
    use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::{PrimeCharacteristicRing, extension::BinomialExtensionField};
    use p3_fri::{HidingFriPcs, create_test_fri_config_zk};
    use p3_matrix::dense::DenseMatrix;
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use rand::{SeedableRng, rngs::SmallRng};

    use crate::{ProverConstraintFolder, StarkConfig, StarkGenericConfig, Val, prove};

    use super::*;

    /// A test AIR that enforces a simple linear transition logic:
    /// - Each cell in the next row must equal the current cell plus 1 (i.e., `next = current + 1`)
    /// - On the last row, the current row must match the provided public values.
    ///
    /// This is useful for validating constraint evaluation, transition logic,
    /// and row condition flags (first/last/transition).
    #[derive(Debug)]
    struct RowLogicAir<const W: usize>;

    struct ColumnShuffleAir;

    impl<F: Field, const W: usize> BaseAir<F> for RowLogicAir<W> {
        fn width(&self) -> usize {
            W
        }
    }

    impl<F: Field> BaseAir<F> for ColumnShuffleAir {
        fn width(&self) -> usize {
            1
        }
    }

    impl<F: Field, const W: usize> BaseAirWithPublicValues<F> for RowLogicAir<W> {}

    impl<PB: InteractionAirBuilder + AirBuilderWithPublicValues, const W: usize> Air<PB>
        for RowLogicAir<W>
    {
        fn eval(&self, builder: &mut PB) {
            let main = builder.main();

            let top = main.row_slice(0).unwrap();
            let bottom = main.row_slice(1).unwrap();

            for col in 0..W {
                let a = *top.get(col).unwrap();
                let b = *bottom.get(col).unwrap();

                // New logic: enforce row[i+1] = row[i] + 1, only on transitions
                builder.when_transition().assert_eq(b, a + PB::F::ONE);
            }

            let a = vec![top.get(0).unwrap()];

            builder.register_interaction(a.into_iter().cloned(), PB::F::ONE);
            builder.constrain_cumulative_sum();

            let mut builder = builder.when(builder.is_last_row());

            // Add public value equality on last row for extra coverage
            let public_values = builder.public_values().to_vec();

            for (i, pv) in public_values.into_iter().enumerate().take(W) {
                builder.assert_eq(*top.get(i).unwrap(), pv);
            }
        }
    }

    impl<F: Field, ExtF: ExtensionField<F>>
        Air<LogupInteractionAirBuilder<'_, DebugConstraintBuilder<'_, F, ExtF>>>
        for ColumnShuffleAir
    {
        fn eval(
            &self,
            builder: &mut LogupInteractionAirBuilder<'_, DebugConstraintBuilder<'_, F, ExtF>>,
        ) {
            let main = builder.main();

            let a = vec![main.top.get(0, 0).unwrap()];

            builder.register_interaction(a.into_iter(), -F::ONE);
            builder.constrain_cumulative_sum();
        }
    }

    // #[test]
    // fn test_incremental_rows_with_last_row_check() {
    //     // Each row = previous + 1, with 4 rows total, 2 columns.
    //     // Last row must match public values [4, 4]
    //     let air = RowLogicAir::<2>;
    //     let values = vec![
    //         BabyBear::ONE,
    //         BabyBear::ONE, // Row 0
    //         BabyBear::new(2),
    //         BabyBear::new(2), // Row 1
    //         BabyBear::new(3),
    //         BabyBear::new(3), // Row 2
    //         BabyBear::new(4),
    //         BabyBear::new(4), // Row 3 (last)
    //     ];
    //     let main = RowMajorMatrix::new(values, 2);
    //     let permutation: DenseMatrix<BinomialExtensionField<BabyBear, 4>> = RowMajorMatrix::new(vec![], 0);
    //     check_multitable_constraints(
    //         &[air],
    //         &[main],
    //         &[permutation],
    //          &vec![BabyBear::new(4); 2]
    //     );
    // }

    // #[test]
    // #[should_panic]
    // fn test_incorrect_increment_logic() {
    //     // Row 2 does not equal row 1 + 1 → should fail on transition from row 1 to 2.
    //     let air = RowLogicAir::<2>;
    //     let values = vec![
    //         BabyBear::ONE,
    //         BabyBear::ONE, // Row 0
    //         BabyBear::new(2),
    //         BabyBear::new(2), // Row 1
    //         BabyBear::new(5),
    //         BabyBear::new(5), // Row 2 (wrong)
    //         BabyBear::new(6),
    //         BabyBear::new(6), // Row 3
    //     ];
    //     let main = RowMajorMatrix::new(values, 2);
    //     let permutation: DenseMatrix<BinomialExtensionField<BabyBear, 4>> = RowMajorMatrix::new(vec![], 0);
    //     check_multitable_constraints(
    //         &[air],
    //         &[main],
    //         &[permutation],
    //         &vec![BabyBear::new(6); 2]
    //     );
    // }

    // #[test]
    // #[should_panic]
    // fn test_wrong_last_row_public_value() {
    //     // The transition logic is fine, but public value check fails at the last row.
    //     let air = RowLogicAir::<2>;
    //     let values = vec![
    //         BabyBear::ONE,
    //         BabyBear::ONE, // Row 0
    //         BabyBear::new(2),
    //         BabyBear::new(2), // Row 1
    //         BabyBear::new(3),
    //         BabyBear::new(3), // Row 2
    //         BabyBear::new(4),
    //         BabyBear::new(4), // Row 3
    //     ];
    //     let main = RowMajorMatrix::new(values, 2);
    //     let permutation: DenseMatrix<BinomialExtensionField<BabyBear, 4>> = RowMajorMatrix::new(vec![
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //         BinomialExtensionField::default(),
    //     ], 1);
    //     // Wrong public value on column 1
    //     check_multitable_constraints(
    //         &[air],
    //         &[main],
    //         &[permutation],
    //         &vec![BabyBear::new(4), BabyBear::new(5)]
    //     );
    // }

    #[test]
    fn test_single_row_wraparound_logic() {
        type Val = BabyBear;
        type Challenge = BinomialExtensionField<Val, 4>;

        type Perm = Poseidon2BabyBear<16>;
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);

        type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
        let hash = MyHash::new(perm.clone());

        type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
        let compress = MyCompress::new(perm.clone());

        type ValMmcs = MerkleTreeHidingMmcs<
            <Val as Field>::Packing,
            <Val as Field>::Packing,
            MyHash,
            MyCompress,
            SmallRng,
            8,
            4,
        >;

        let val_mmcs = ValMmcs::new(hash, compress, rng);

        type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

        type Dft = Radix2DitParallel<Val>;
        let dft = Dft::default();

        type Challenger = DuplexChallenger<Val, Perm, 16, 8>;

        let fri_config = create_test_fri_config_zk(challenge_mmcs);
        type HidingPcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
        let pcs = HidingPcs::new(dft, val_mmcs, fri_config, 4, SmallRng::seed_from_u64(1));
        type MyConfig = StarkConfig<HidingPcs, Challenge, Challenger>;
        let challenger = Challenger::new(perm);
        let config = MyConfig::new(pcs, challenger);

        let challenge_0 = BinomialExtensionField::from(BabyBear::from_u8(5));
        let challenge_2 = BinomialExtensionField::from(BabyBear::from_u8(15));

        let val_0 = BabyBear::new(98);
        let val_1 = BabyBear::new(77);

        let perm_0 = (challenge_2 - (challenge_0 + val_0)).inverse();
        let perm_1 = (challenge_2 - (challenge_0 + val_0 + BabyBear::ONE)).inverse();
        println!("Perm0: {perm_0:?}");
        println!("Perm1: {perm_1:?}");

        let cumulative_sum = perm_0 + perm_1;
        println!("Cumulative sum: {cumulative_sum:?}");

        // A single-row matrix still performs a wraparound check with itself.
        // row[0] == row[0] + 1 ⇒ fails unless handled properly by transition logic.
        // Here: is_transition == false ⇒ so no assertions are enforced.
        let row_air = RowLogicAir::<2>;
        let row_values = vec![
            val_0,
            val_1, // Row 0
            val_0 + BabyBear::ONE,
            val_1 + BabyBear::ONE, // Row 1
        ];
        let row_main = RowMajorMatrix::new(row_values, 2);
        let row_permutation: DenseMatrix<BinomialExtensionField<BabyBear, 4>> = RowMajorMatrix::new(
            vec![perm_0 + perm_1, cumulative_sum, perm_1, cumulative_sum],
            2,
        );

        let shuffle_air = ColumnShuffleAir;
        let shuffle_values = vec![val_0 + BabyBear::ONE, val_0];

        prove::<MyConfig, RowLogicAir<2>>(
            &config,
            &row_air,
            row_main,
            row_permutation,
            &vec![val_0 + BabyBear::ONE, val_1 + BabyBear::ONE],
        );

        // check_multitable_constraints(
        //     &row_air,
        //     &row_main,
        //     &row_permutation,
        //     &vec![val_0 + BabyBear::ONE, val_1 + BabyBear::ONE]
        // );
        // check_multitable_constraints(
        //     &shuffle_air,
        //     &shuffle_main,
        //     &shuffle_permutation,
        //     &vec![]
        // );
        // check_cumulative_sum::<BabyBear, _>(&[row_permutation, shuffle_permutation]);
    }
}
