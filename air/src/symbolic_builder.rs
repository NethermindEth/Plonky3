use alloc::vec;
use alloc::vec::Vec;

use p3_field::{Algebra, ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_ceil_usize;
use tracing::instrument;

use crate::{Air, AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, InteractionAirBuilder, PairBuilder, PermutationAirBuilder};
use crate::symbolic_variable::Entry;
use crate::symbolic_expression::SymbolicExpression;
use crate::symbolic_variable::SymbolicVariable;

#[instrument(name = "infer log of constraint degree", skip_all)]
pub fn get_log_quotient_degree<F, EF, Challenge, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
    is_zk: usize,
) -> usize
where
    F: Field,
    EF: Clone + Send + Sync,
    A: Air<SymbolicAirBuilder<F, EF, Challenge>>,
{
    assert!(is_zk <= 1, "is_zk must be either 0 or 1");
    // We pad to at least degree 2, since a quotient argument doesn't make sense with smaller degrees.
    let constraint_degree =
        (get_max_constraint_degree(air, preprocessed_width, num_public_values) + is_zk).max(2);

    // The quotient's actual degree is approximately (max_constraint_degree - 1) n,
    // where subtracting 1 comes from division by the vanishing polynomial.
    // But we pad it to a power of two so that we can efficiently decompose the quotient.
    log2_ceil_usize(constraint_degree - 1)
}

#[instrument(name = "infer constraint degree", skip_all, level = "debug")]
pub fn get_max_constraint_degree<F, EF, Challenge, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
) -> usize
where
    F: Field,
    EF: Clone + Send + Sync,
    A: Air<SymbolicAirBuilder<F, EF, Challenge>>,
{
    get_symbolic_constraints(air, preprocessed_width, num_public_values)
        .iter()
        .map(|c| c.degree_multiple())
        .max()
        .unwrap_or(0)
}

#[instrument(name = "evaluate constraints symbolically", skip_all, level = "debug")]
pub fn get_symbolic_constraints<F, EF, Challenge, A>(
    air: &A,
    preprocessed_width: usize,
    num_public_values: usize,
) -> Vec<SymbolicExpression<F>>
where
    F: Field,
    EF: Clone + Send + Sync,
    A: Air<SymbolicAirBuilder<F, EF, Challenge>>,
{
    let mut builder = SymbolicAirBuilder::new(preprocessed_width, air.width(), num_public_values, 0);
    air.eval(&mut builder);
    builder.base_constraints().clone()
}

#[derive(Clone, Debug)]
pub struct Interaction<F> {
    data: Vec<F>,
    multiplicity: F,
}

impl<F> Interaction<F> {
    pub fn data(&self) -> &Vec<F> {
        &(self.data)
    }

    pub fn multiplicity(&self) -> &F {
        &(self.multiplicity)
    }
}

/// An `AirBuilder` for evaluating constraints symbolically, and recording them for later use.
#[derive(Debug)]
pub struct SymbolicAirBuilder<F, EF, Challenge> {
    preprocessed: RowMajorMatrix<SymbolicVariable<F>>,
    main: RowMajorMatrix<SymbolicVariable<F>>,
    permutation: RowMajorMatrix<SymbolicVariable<EF>>,
    public_values: Vec<SymbolicVariable<F>>,
    challenges: Vec<SymbolicVariable<Challenge>>,
    base_constraints: Vec<SymbolicExpression<F>>,
    extension_constraints: Vec<SymbolicExpression<EF>>,
    interactions: Vec<Interaction<SymbolicExpression<F>>>,
}

impl<F, EF, Challenge> SymbolicAirBuilder<F, EF, Challenge>
where
    F: Clone + Send + Sync,
    EF: Clone + Send + Sync
{
    pub fn new(preprocessed_width: usize, width: usize, num_public_values: usize, num_challenges: usize) -> Self {
        let prep_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..preprocessed_width)
                    .map(move |index| SymbolicVariable::new(Entry::Preprocessed { offset }, index))
            })
            .collect();
        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..width).map(move |index| SymbolicVariable::new(Entry::Main { offset }, index))
            })
            .collect();
        let permutation_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..width).map(move |index| SymbolicVariable::new(Entry::Permutation { offset }, index))
            })
            .collect();
        let public_values = (0..num_public_values)
            .map(move |index| SymbolicVariable::new(Entry::Public, index))
            .collect();
        let challenges = (0..num_challenges)
            .map(move |index| SymbolicVariable::new(Entry::Challenge, index))
            .collect();
        Self {
            preprocessed: RowMajorMatrix::new(prep_values, preprocessed_width),
            main: RowMajorMatrix::new(main_values, width),
            permutation: RowMajorMatrix::new(permutation_values, width),
            public_values,
            challenges,
            base_constraints: vec![],
            extension_constraints: vec![],
            interactions: vec![],
        }
    }

    pub fn base_constraints(&self) -> &Vec<SymbolicExpression<F>> {
        &(self.base_constraints)
    }

    pub fn extension_constraints(&self) -> &Vec<SymbolicExpression<EF>> {
        &(self.extension_constraints)
    }

    pub fn interactions(&self) -> &Vec<Interaction<SymbolicExpression<F>>> {
        &(self.interactions)
    }
}

impl<F, EF, Challenge> AirBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field
{
    type F = F;
    type Expr = SymbolicExpression<F>;
    type Var = SymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    /// # Panics
    /// This function panics if `size` is not `2`.
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.base_constraints.push(x.into());
    }
}

impl<F, EF, Challenge> AirBuilderWithPublicValues for SymbolicAirBuilder<F, EF, Challenge>
where F: Field
{
    type PublicVar = SymbolicVariable<F>;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F, EF, Challenge> PairBuilder for SymbolicAirBuilder<F, EF, Challenge>
where F: Field
{
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F, EF, Challenge> ExtensionBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>
{
    type EF = EF;

    type ExprEF = SymbolicExpression<EF>;

    type VarEF = SymbolicVariable<EF>;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF> {
        self.extension_constraints.push(x.into())
    }
}

impl <F, EF, Challenge> PermutationAirBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>,
    SymbolicExpression<EF>: From<SymbolicVariable<Challenge>>,
    Challenge: Copy,
{
    type MP = RowMajorMatrix<Self::VarEF>;

    type RandomVar = SymbolicVariable<Challenge>;

    fn permutation(&self) -> Self::MP {
        self.permutation.clone()
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        self.challenges.as_slice()
    }
}

impl <F, EF, Challenge> InteractionAirBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field
{
    fn register_interaction<Data: Iterator<Item: Into<Self::Expr>>, Count: Into<Self::Expr>>(&mut self, data: Data, count: Count) {
        self.interactions.push(Interaction {
            data: data.map(|x| x.into()).collect(),
            multiplicity: count.into()
        });
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use crate::BaseAir;
    use p3_baby_bear::BabyBear;

    use super::*;

    #[derive(Debug)]
    struct MockAir {
        constraints: Vec<SymbolicVariable<BabyBear>>,
        width: usize,
    }

    impl BaseAir<BabyBear> for MockAir {
        fn width(&self) -> usize {
            self.width
        }
    }

    impl Air<SymbolicAirBuilder<BabyBear, (), ()>> for MockAir {
        fn eval(&self, builder: &mut SymbolicAirBuilder<BabyBear, (), ()>) {
            for constraint in &self.constraints {
                builder.assert_zero(*constraint);
            }
        }
    }

    #[test]
    fn test_get_log_quotient_degree_no_constraints() {
        let air = MockAir {
            constraints: vec![],
            width: 4,
        };
        let log_degree = get_log_quotient_degree(&air, 3, 2, 0);
        assert_eq!(log_degree, 0);
    }

    #[test]
    fn test_get_log_quotient_degree_single_constraint() {
        let air = MockAir {
            constraints: vec![SymbolicVariable::new(Entry::Main { offset: 0 }, 0)],
            width: 4,
        };
        let log_degree = get_log_quotient_degree(&air, 3, 2, 0);
        assert_eq!(log_degree, log2_ceil_usize(1));
    }

    #[test]
    fn test_get_log_quotient_degree_multiple_constraints() {
        let air = MockAir {
            constraints: vec![
                SymbolicVariable::new(Entry::Main { offset: 0 }, 0),
                SymbolicVariable::new(Entry::Main { offset: 1 }, 1),
                SymbolicVariable::new(Entry::Main { offset: 2 }, 2),
            ],
            width: 4,
        };
        let log_degree = get_log_quotient_degree(&air, 3, 2, 0);
        assert_eq!(log_degree, log2_ceil_usize(1));
    }

    #[test]
    fn test_get_max_constraint_degree_no_constraints() {
        let air = MockAir {
            constraints: vec![],
            width: 4,
        };
        let max_degree = get_max_constraint_degree(&air, 3, 2);
        assert_eq!(
            max_degree, 0,
            "No constraints should result in a degree of 0"
        );
    }

    #[test]
    fn test_get_max_constraint_degree_multiple_constraints() {
        let air = MockAir {
            constraints: vec![
                SymbolicVariable::new(Entry::Main { offset: 0 }, 0),
                SymbolicVariable::new(Entry::Main { offset: 1 }, 1),
                SymbolicVariable::new(Entry::Main { offset: 2 }, 2),
            ],
            width: 4,
        };
        let max_degree = get_max_constraint_degree(&air, 3, 2);
        assert_eq!(max_degree, 1, "Max constraint degree should be 1");
    }

    #[test]
    fn test_get_symbolic_constraints() {
        let c1 = SymbolicVariable::new(Entry::Main { offset: 0 }, 0);
        let c2 = SymbolicVariable::new(Entry::Main { offset: 1 }, 1);

        let air = MockAir {
            constraints: vec![c1, c2],
            width: 4,
        };

        let constraints = get_symbolic_constraints(&air, 3, 2);

        assert_eq!(constraints.len(), 2, "Should return exactly 2 constraints");

        assert!(
            constraints.iter().any(|x| matches!(x, SymbolicExpression::Variable(v) if v.index == c1.index && v.entry == c1.entry)),
            "Expected constraint {:?} was not found",
            c1
        );

        assert!(
            constraints.iter().any(|x| matches!(x, SymbolicExpression::Variable(v) if v.index == c2.index && v.entry == c2.entry)),
            "Expected constraint {:?} was not found",
            c2
        );
    }

    #[test]
    fn test_symbolic_air_builder_initialization() {
        let builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);

        let expected_main = [
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 0),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 1),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 2),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 3),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 0),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 1),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 2),
            SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 3),
        ];

        let builder_main = builder.main.values;

        assert_eq!(
            builder_main.len(),
            expected_main.len(),
            "Main matrix should have the expected length"
        );

        for (expected, actual) in expected_main.iter().zip(builder_main.iter()) {
            assert_eq!(expected.index, actual.index, "Index mismatch");
            assert_eq!(expected.entry, actual.entry, "Entry mismatch");
        }
    }

    #[test]
    fn test_symbolic_air_builder_is_first_last_row() {
        let builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);

        assert!(
            matches!(builder.is_first_row(), SymbolicExpression::IsFirstRow),
            "First row condition did not match"
        );

        assert!(
            matches!(builder.is_last_row(), SymbolicExpression::IsLastRow),
            "Last row condition did not match"
        );
    }

    #[test]
    fn test_symbolic_air_builder_assert_zero() {
        let mut builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);
        let expr = SymbolicExpression::Constant(BabyBear::new(5));
        builder.assert_zero(expr.clone());

        let constraints = builder.base_constraints();
        assert_eq!(constraints.len(), 1, "One constraint should be recorded");

        assert!(
            constraints.iter().any(
                |x| matches!(x, SymbolicExpression::Constant(val) if *val == BabyBear::new(5))
            ),
            "Constraint should match the asserted one"
        );
    }
}
