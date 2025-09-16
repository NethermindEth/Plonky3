use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

use crate::{
    AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, ExtensionBuilderWithRlc,
    InteractionAirBuilder, PermutationAirBuilder,
};

#[derive(Debug)]
pub struct LogupInteractionAirBuilder<'inner, AB: PermutationAirBuilder> {
    pub inner: &'inner mut AB,
    interaction_count: usize,
}

impl<'inner, AB: PermutationAirBuilder> LogupInteractionAirBuilder<'inner, AB> {
    pub fn new(inner: &'inner mut AB) -> Self {
        Self {
            inner,
            interaction_count: 0,
        }
    }

    pub fn get_interaction_count(&self) -> usize {
        self.interaction_count
    }
}

impl<'inner, AB: PermutationAirBuilder> AirBuilder for LogupInteractionAirBuilder<'inner, AB> {
    type F = AB::F;
    type Expr = AB::Expr;
    type Var = AB::Var;
    type M = AB::M;

    fn main(&self) -> Self::M {
        self.inner.main()
    }

    fn is_first_row(&self) -> Self::Expr {
        self.inner.is_first_row()
    }

    fn is_last_row(&self) -> Self::Expr {
        self.inner.is_last_row()
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.inner.is_transition_window(size)
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.inner.assert_zero(x)
    }
}

impl<'inner, AB: AirBuilderWithPublicValues + PermutationAirBuilder> AirBuilderWithPublicValues
    for LogupInteractionAirBuilder<'inner, AB>
{
    type PublicVar = AB::PublicVar;

    fn public_values(&self) -> &[Self::PublicVar] {
        self.inner.public_values()
    }
}

impl<'inner, AB: PermutationAirBuilder> ExtensionBuilder
    for LogupInteractionAirBuilder<'inner, AB>
{
    type EF = AB::EF;
    type ExprEF = AB::ExprEF;
    type VarEF = AB::VarEF;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.inner.assert_zero_ext(x)
    }
}

impl<'inner, AB: PermutationAirBuilder> ExtensionBuilderWithRlc
    for LogupInteractionAirBuilder<'inner, AB>
{
    fn calculate_rlc<Data: Iterator<Item: Into<Self::Expr>>>(&self, data: Data) -> Self::ExprEF {
        let challenges = self.inner.permutation_randomness();
        let alpha: Self::ExprEF = challenges[0].into();
        let beta: Self::ExprEF = challenges[1].into();
        let beta_powers = beta.powers();

        alpha
            + beta_powers
                .zip(data)
                .map(|(power, val)| power * val.into())
                .sum::<Self::ExprEF>()
    }
}

impl<'inner, AB: PermutationAirBuilder> InteractionAirBuilder
    for LogupInteractionAirBuilder<'inner, AB>
{
    fn register_interaction<Data: Iterator<Item: Into<Self::Expr>>, Count: Into<Self::Expr>>(
        &mut self,
        data: Data,
        count: Count,
    ) {
        let data: Vec<Self::Expr> = data.map(|x| x.into()).collect();
        let count: Self::Expr = count.into();

        let permutation_trace = self.inner.permutation().to_row_major_matrix();

        let permutation_trace_entry: <Self as ExtensionBuilder>::ExprEF = (*permutation_trace
            .row_slice(0)
            .unwrap()
            .get(self.interaction_count)
            .expect("Not enough permutation trace columns for LogupInteractionAirBuilder"))
        .into();

        let permutation_trace_entry_next: <Self as ExtensionBuilder>::ExprEF = (*permutation_trace
            .row_slice(1)
            .unwrap()
            .get(self.interaction_count)
            .expect("Not enough permutation trace columns for LogupInteractionAirBuilder"))
        .into();

        let rlc = self.calculate_rlc(data.clone().into_iter());
        let offset: <Self as ExtensionBuilder>::ExprEF =
            self.inner.permutation_randomness()[2].into();

        // entry[last_row] = sum[all_rows](count / (offset - rlc))

        let is_last: <Self as ExtensionBuilder>::ExprEF = self.is_last_row().into();
        let is_transition: <Self as ExtensionBuilder>::ExprEF = self.is_transition().into();

        self.assert_eq_ext(
            is_last.clone() * count.clone(),
            is_last.clone() * permutation_trace_entry.clone() * (offset.clone() - rlc.clone()),
        );

        self.assert_eq_ext(
            is_transition.clone() * count,
            is_transition
                * (permutation_trace_entry - permutation_trace_entry_next)
                * (offset - rlc),
        );

        self.interaction_count += 1;
    }
}

