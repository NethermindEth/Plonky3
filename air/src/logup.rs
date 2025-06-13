use p3_field::{Algebra, ExtensionField, Field, PrimeCharacteristicRing};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

use crate::{symbolic_builder::SymbolicAirBuilder, symbolic_expression::SymbolicExpression, symbolic_variable::SymbolicVariable, AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, ExtensionBuilderWithRlc, InteractionAirBuilder, PermutationAirBuilder};

pub struct SymbolicLogupInteractionAirBuilder<F, EF, Challenge> {
    builder: SymbolicAirBuilder<F, EF, Challenge>
}

impl<F, EF, Challenge> SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where
    F: Clone + Send + Sync,
    EF: Clone + Send + Sync
{
    pub fn new(preprocessed_width: usize, width: usize, num_public_values: usize, num_challenges: usize) -> Self {
        Self {
            builder: SymbolicAirBuilder::<F, EF, Challenge>::new(preprocessed_width, width, num_public_values, num_challenges)
        }
    }
}

impl<F, EF, Challenge> SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>,
    SymbolicExpression<EF>: From<SymbolicVariable<Challenge>>,
    Challenge: Copy
{
    pub fn interaction_count(&self) -> usize {
        self.builder.interactions().len()
    }

    pub fn finalise_constraints(mut self) -> Vec<SymbolicExpression<EF>> {
        self.constrain_cumulative_sum();

        let base_constraints = self
            .builder
            .base_constraints()
            .clone();

        let extension_constraints = self
            .builder
            .extension_constraints()
            .clone();

        extension_constraints
            .into_iter()
            .chain(base_constraints.into_iter().map(|x| x.into()))
            .collect()
    }
}

impl <F, EF, Challenge> AirBuilder for SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where 
    F: Field
{
    type F = F;

    type Expr = SymbolicExpression<F>;

    type Var = SymbolicVariable<F>;

    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.builder.main()
    }

    fn is_first_row(&self) -> Self::Expr {
        self.builder.is_first_row()
    }

    fn is_last_row(&self) -> Self::Expr {
        self.builder.is_last_row()
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.builder.is_transition_window(size)
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.builder.assert_zero(x)
    }
}

impl<F, EF, Challenge> AirBuilderWithPublicValues for SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where F: Field
{
    type PublicVar = SymbolicVariable<F>;
    fn public_values(&self) -> &[Self::PublicVar] {
        self.builder.public_values()
    }
}

impl <F, EF, Challenge> ExtensionBuilder for SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
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
        self.builder.assert_zero_ext(x)
    }
}

impl<F, EF, Challenge> ExtensionBuilderWithRlc for SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>,
    SymbolicExpression<EF>: From<SymbolicVariable<Challenge>>,
    Challenge: Copy,
{
    fn calculate_rlc<Data: Iterator<Item: Into<Self::Expr>>>(&self, data: Data) -> Self::ExprEF {
        let challenges = self.builder.permutation_randomness();
        let alpha: SymbolicExpression<EF> = challenges[0].into();
        let beta: SymbolicExpression<EF> = challenges[1].into();
        let beta_powers = beta.powers();

        alpha +
            beta_powers
                .zip(data)
                .map(|(power, val)| {
                    power * val.into()
                })
                .sum::<SymbolicExpression<EF>>()
    }
}

impl<F, EF, Challenge> InteractionAirBuilder for SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>,
    SymbolicExpression<EF>: From<SymbolicVariable<Challenge>>,
    Challenge: Copy,
{
    fn register_interaction<Data: Iterator<Item: Into<Self::Expr>>, Count: Into<Self::Expr>>(&mut self, data: Data, count: Count) {
        let interaction_idx = self.builder.interactions().len();
        
        let data: Vec<Self::Expr> = data.map(|x| x.into()).collect();
        let count: Self::Expr = count.into();

        let permutation_trace = self
            .builder
            .permutation()
            .to_row_major_matrix();
    
        let permutation_trace_entry: SymbolicExpression<EF> = permutation_trace.row_slice(0).unwrap()[interaction_idx].into();
        let rlc = self.calculate_rlc(data.clone().into_iter());
        let offset: SymbolicExpression<EF> = self.builder.permutation_randomness()[2].into();
        self.builder.assert_eq_ext(count.clone(), permutation_trace_entry * (offset - rlc));

        self.builder.register_interaction(data.into_iter(), count);
    }
}

impl <F, EF, Challenge> SymbolicLogupInteractionAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF> : Algebra<SymbolicExpression<F>>,
    SymbolicExpression<EF>: From<SymbolicVariable<Challenge>>,
    Challenge: Copy,
{
    pub fn constrain_cumulative_sum(&mut self) {
        let permutation_trace = self
            .builder
            .permutation()
            .to_row_major_matrix();

        let permutation_local = permutation_trace.row_slice(0).unwrap();
        let permutation_next = permutation_trace.row_slice(1).unwrap();
        let interaction_count = self.builder.interactions().len();

        // Constrain column to be constant
        self.builder.assert_eq_ext(permutation_local[interaction_count], permutation_next[interaction_count]);

        // Constrain column to match complete cumulative sum

        let sum: SymbolicExpression<EF> = (0..interaction_count)
            .map(|idx| permutation_local[idx].into())
            .sum();

        let is_last_row: SymbolicExpression<EF> = self.builder.is_last_row().into();

        self.builder.assert_eq_ext(is_last_row.clone() * sum, is_last_row * permutation_local[interaction_count]);
    }
}