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
