use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::logup::LogupInteractionAirBuilder;
use p3_air::symbolic_builder::SymbolicAirBuilder;
use p3_air::symbolic_expression::SymbolicExpression;
use p3_air::{Air, BaseAir};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, PackedValue, PrimeCharacteristicRing};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::{Matrix, stack::VerticalPair};
use p3_maybe_rayon::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use tracing::{debug_span, info_span, instrument};

use crate::{
    Commitments, Domain, OpenedValues, PackedChallenge, PackedVal, Proof, ProverConstraintFolder,
    StarkGenericConfig, Val, VerifierConstraintFolder,
};

pub trait QuotientAir<SC>:
    for<'a> Air<LogupInteractionAirBuilder<'a, ProverConstraintFolder<'a, SC>>>
where
    SC: StarkGenericConfig,
{
}
impl<T, SC> QuotientAir<SC> for T
where
    T: for<'a> Air<LogupInteractionAirBuilder<'a, ProverConstraintFolder<'a, SC>>>,
    SC: StarkGenericConfig,
{
}
pub trait VerifiableLogupAir<SC>:
    for<'a> Air<LogupInteractionAirBuilder<'a, VerifierConstraintFolder<'a, SC>>>
where
    SC: StarkGenericConfig,
{
}
impl<T, SC> VerifiableLogupAir<SC> for T
where
    T: for<'a> Air<LogupInteractionAirBuilder<'a, VerifierConstraintFolder<'a, SC>>>,
    SC: StarkGenericConfig,
{
}
pub trait LogupAir<SC>:
    Air<
        SymbolicAirBuilder<
            Val<SC>,
            <SC as StarkGenericConfig>::Challenge,
            <SC as StarkGenericConfig>::Challenge,
        >,
    > + QuotientAir<SC>
    + VerifiableLogupAir<SC>
where
    SC: StarkGenericConfig,
{
}
impl<T, SC> LogupAir<SC> for T
where
    T: Air<
            SymbolicAirBuilder<
                Val<SC>,
                <SC as StarkGenericConfig>::Challenge,
                <SC as StarkGenericConfig>::Challenge,
            >,
        > + QuotientAir<SC>
        + VerifiableLogupAir<SC>,
    SC: StarkGenericConfig,
{
}

#[instrument(name = "infer log of constraint degree", skip_all)]
pub fn get_log_quotient_degree<SC>(
    air: &Box<dyn LogupAir<SC>>,
    preprocessed_width: usize,
    num_public_values: usize,
    is_zk: usize,
) -> usize
where
    SC: StarkGenericConfig,
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
pub fn get_max_constraint_degree<SC>(
    air: &Box<dyn LogupAir<SC>>,
    preprocessed_width: usize,
    num_public_values: usize,
) -> usize
where
    SC: StarkGenericConfig,
{
    get_symbolic_constraints(air, preprocessed_width, num_public_values)
        .iter()
        .map(|c| c.degree_multiple())
        .max()
        .unwrap_or(0)
}

#[instrument(name = "evaluate constraints symbolically", skip_all, level = "debug")]
pub fn get_symbolic_constraints<SC>(
    air: &Box<dyn LogupAir<SC>>,
    preprocessed_width: usize,
    num_public_values: usize,
) -> Vec<SymbolicExpression<SC::Challenge>>
where
    SC: StarkGenericConfig,
{
    let mut builder = SymbolicAirBuilder::new(
        preprocessed_width,
        <dyn LogupAir<SC> as BaseAir<Val<SC>>>::width(air.as_ref()),
        num_public_values,
        0,
    );
    air.eval(&mut builder);
    let mut constraints = Vec::new();

    constraints.extend_from_slice(builder.extension_constraints());
    constraints.append(
        &mut builder
            .base_constraints()
            .iter()
            .map(|x| x.map(&|&x| x.into()))
            .collect(),
    );

    constraints
}

#[instrument(skip_all)]
#[allow(clippy::multiple_bound_locations)] // cfg not supported in where clauses?
pub fn prove<
    SC,
    // todo put these back in
    // #[cfg(debug_assertions)] A: for<'a> Air<crate::check_constraints::DebugConstraintBuilder<'a, Val<SC>>>,
    // #[cfg(not(debug_assertions))] A,
>(
    config: &SC,
    airs: &[Box<dyn LogupAir<SC>>],
    traces: &[RowMajorMatrix<Val<SC>>],
    permutation_traces: &[RowMajorMatrix<SC::Challenge>],
    public_values: &[Vec<Val<SC>>],
) -> Vec<(Proof<SC>, <SC as StarkGenericConfig>::Challenge)>
where
    SC: StarkGenericConfig,
    // A: LogupAir<SC>,
{
    let mut proofs = vec![];

    for i in 0..airs.len() {
        let air = &airs[i];
        let trace = &traces[i];
        let permutation_trace = &permutation_traces[i];
        let public_values = &public_values[i];

        // TODO put back in
        // #[cfg(debug_assertions)]
        // crate::check_constraints::check_constraints(air, &trace, public_values);
        //
        let pcs = config.pcs();

        let degree = trace.height();
        let log_degree = log2_strict_usize(degree);
        let log_ext_degree = log_degree + config.is_zk();

        let symbolic_constraints = get_symbolic_constraints(air, 0, public_values.len());
        // TODO: this shouldn't be ten. But somehow we have fewer challenges than constraints.
        let constraint_count = symbolic_constraints.len() + public_values.len() + 1;
        let constraint_degree = symbolic_constraints
            .iter()
            .map(SymbolicExpression::degree_multiple)
            .max()
            .unwrap_or(0);
        let log_quotient_degree = log2_ceil_usize(constraint_degree - 1 + config.is_zk());
        let quotient_degree = 1 << (log_quotient_degree + config.is_zk());

        let mut challenger = config.initialise_challenger();
        let trace_domain = pcs.natural_domain_for_degree(degree);
        let ext_trace_domain = pcs.natural_domain_for_degree(degree * (config.is_zk() + 1));
        let (trace_commit, trace_data) = info_span!("commit to trace data")
            .in_scope(|| pcs.commit([(ext_trace_domain, trace.clone())]));

        // Observe the instance.
        // degree < 2^255 so we can safely cast log_degree to a u8.
        challenger.observe(Val::<SC>::from_u8(log_ext_degree as u8));
        challenger.observe(Val::<SC>::from_u8(log_degree as u8));
        // TODO: Might be best practice to include other instance data here; see verifier comment.

        challenger.observe(trace_commit.clone());
        challenger.observe_slice(public_values);

        //TODO unshadow permutation_trace?
        let permutation_trace_flat = permutation_trace.clone().flatten_to_base();
        println!(
            "Flat height: {}\n Domain size: {}",
            permutation_trace_flat.height(),
            trace_domain.size()
        );
        let (permutation_commit, permutation_data) =
            pcs.commit([(trace_domain, permutation_trace_flat)]);

        challenger.observe(permutation_commit.clone());

        // Get the first Fiat Shamir challenge which will be used to combine all constraint polynomials
        // into a single polynomial.
        //
        // Soundness Error:
        // If a prover is malicious, we can find a row `i` such that some of the constraints
        // C_0, ..., C_n are non 0 on this row. The malicious prover "wins" if the random challenge
        // alpha is such that:
        // (1): C_0(i) + alpha * C_1(i) + ... + alpha^n * C_n(i) = 0
        // This is a polynomial of degree n, so it has at most n roots. Thus the probability of this
        // occurring for a given trace and set of constraints is n/|EF|.
        //
        // Currently, we do not observe data about the constraint polynomials directly. In particular
        // a prover could take a trace and fiddle around with the AIR it claims to satisfy without
        // changing this sample alpha.
        //
        // In particular this means that a malicious prover could create a custom AIR for a given trace
        // such that equation (1) holds. However, such AIRs would need to be very specific and
        // so such tampering should be obvious to spot. The verifier needs to check the AIR anyway to
        // confirm that satisfying it indeed proves what the prover claims. Hence this should not be
        // a soundness issue.
        let alpha: SC::Challenge = challenger.sample_algebra_element();

        let quotient_domain =
            ext_trace_domain.create_disjoint_domain(1 << (log_ext_degree + log_quotient_degree));

        let trace_on_quotient_domain =
            pcs.get_evaluations_on_domain(&trace_data, 0, quotient_domain);
        let permutation_trace_on_quotient_domain =
            pcs.get_evaluations_on_domain(&permutation_data, 0, quotient_domain);

        let perm_challenges = (0..3)
            .map(|_| challenger.sample_algebra_element::<SC::Challenge>().into())
            .collect::<Vec<PackedChallenge<SC>>>();

        let (quotient_values, num_interactions) = quotient_values(
            air,
            public_values,
            trace_domain,
            quotient_domain,
            trace_on_quotient_domain,
            permutation_trace_on_quotient_domain,
            alpha,
            &perm_challenges,
            constraint_count,
        );

        // Due to `alpha`, evaluations of `Q` all lie in the extension field `E`.
        // We flatten this into a matrix of `F` values by treating `E` as an `F`
        // vector space and so separating each element of `E` into `e + 1 = [E: F]` elements of `F`.
        //
        // This is valid to do because our domain lies in the base field `F`. Hence we can split
        // `Q(x)` into `e + 1` polynomials `Q_0(x), ... , Q_e(x)` each contained in `F`.
        // such that `Q(x) = [Q_0(x), ... ,Q_e(x)]` holds for all `x` in `F`.
        let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();

        let cumulative_sum: <SC as StarkGenericConfig>::Challenge = (0..num_interactions)
            .map(|i| {
                permutation_trace
                    .get(0, i)
                    .expect("Permutation trace is not wide enough for number of interactions")
            })
            .sum();
        // challenger.observe_slice(&<SC as StarkGenericConfig>::Challenge::flatten_to_base(
        //     vec![cumulative_sum],
        // ));

        let (quotient_commit, quotient_data) = info_span!("commit to quotient poly chunks")
            .in_scope(|| pcs.commit_quotient(quotient_domain, quotient_flat, quotient_degree));
        challenger.observe(quotient_commit.clone());

        // If zk is enabled, we generate random extension field values of the size of the randomized trace. If `n` is the degree of the initial trace,
        // then the randomized trace has degree `2n`. To randomize the FRI batch polynomial, we then need an extension field random polynomial of degree `2n -1`.
        // So we can generate a random polynomial  of degree `2n`, and provide it to `open` as is.
        // Then the method will add `(R(X) - R(z)) / (X - z)` (which is of the desired degree `2n - 1`), to the batch of polynomials.
        // Since we need a random polynomial defined over the extension field, and the `commit` method is over the base field,
        // we actually need to commit to `SC::CHallenge::D` base field random polynomials.
        // This is similar to what is done for the quotient polynomials.
        // TODO: This approach is only statistically zk. To make it perfectly zk, `R` would have to truly be an extension field polynomial.
        let (opt_r_commit, opt_r_data) = if SC::Pcs::ZK {
            let (r_commit, r_data) = pcs
                .get_opt_randomization_poly_commitment(ext_trace_domain)
                .expect("ZK is enabled, so we should have randomization commitments");
            (Some(r_commit), Some(r_data))
        } else {
            (None, None)
        };

        let commitments = Commitments {
            trace: trace_commit,
            permutation_trace: permutation_commit,
            quotient_chunks: quotient_commit,
            random: opt_r_commit.clone(),
        };

        if let Some(r_commit) = opt_r_commit {
            challenger.observe(r_commit);
        }

        // Get an out-of-domain point to open our values at.
        //
        // Soundness Error:
        // This sample will be used to check the equality: `C(X) = ZH(X)Q(X)`. If a prover is malicious
        // and this equality is false, the probability that it is true at the point `zeta` will be
        // deg(C(X))/|EF| = dN/|EF| where `N` is the trace length and our constraints have degree `d`.
        //
        // Completeness Error:
        // If zeta happens to lie in the domain `gK`, then when opening at zeta we will run into division
        // by zero errors. This doesn't lead to a soundness issue as the verifier will just reject in those
        // cases but it is a completeness issue and contributes a completeness error of |gK| = 2N/|EF|.
        let zeta: SC::Challenge = challenger.sample_algebra_element();
        let zeta_next = trace_domain.next_point(zeta).unwrap();

        let is_random = opt_r_data.is_some();
        let (opened_values, opening_proof) = info_span!("open").in_scope(|| {
            let round0 = opt_r_data.as_ref().map(|r_data| (r_data, vec![vec![zeta]]));
            let round1 = (&trace_data, vec![vec![zeta, zeta_next]]);
            let round2 = (&quotient_data, vec![vec![zeta]; quotient_degree]); // open every chunk at zeta
            let round3 = (&permutation_data, vec![vec![zeta, zeta_next]]);

            let rounds = round0
                .into_iter()
                .chain([round1, round2, round3])
                .collect::<Vec<_>>();

            pcs.open(rounds, &mut challenger)
        });

        let trace_idx = <SC as StarkGenericConfig>::Pcs::TRACE_IDX;
        let quotient_idx = <SC as StarkGenericConfig>::Pcs::QUOTIENT_IDX;
        let permutation_idx = <SC as StarkGenericConfig>::Pcs::PERMUTATION_IDX;
        let trace_local = opened_values[trace_idx][0][0].clone();
        let trace_next = opened_values[trace_idx][0][1].clone();
        // TODO: this has to be changed to handle permutation trace properly.
        // permutation trace index != trace index!!!
        let permutation_trace_local = opened_values[permutation_idx][0][0].clone();
        let permutation_trace_next = opened_values[permutation_idx][0][1].clone();
        let quotient_chunks = opened_values[quotient_idx]
            .iter()
            .map(|v| v[0].clone())
            .collect_vec();
        let random = if is_random {
            Some(opened_values[0][0][0].clone())
        } else {
            None
        };
        let opened_values = OpenedValues {
            trace_local,
            trace_next,
            permutation_trace_local,
            permutation_trace_next,
            quotient_chunks,
            random,
        };
        proofs.push((
            Proof {
                commitments,
                opened_values,
                opening_proof,
                degree_bits: log_ext_degree,
            },
            cumulative_sum,
        ));
    }
    proofs
}

#[instrument(name = "compute quotient polynomial", skip_all)]
// TODO: Group some arguments to remove the `allow`?
#[allow(clippy::too_many_arguments)]
fn quotient_values<SC, Mat>(
    air: &Box<dyn LogupAir<SC>>,
    public_values: &Vec<Val<SC>>,
    trace_domain: Domain<SC>,
    quotient_domain: Domain<SC>,
    trace_on_quotient_domain: Mat,
    permutation_trace_on_quotient_domain: Mat,
    alpha: SC::Challenge,
    perm_challenges: &[PackedChallenge<SC>],
    constraint_count: usize,
) -> (Vec<SC::Challenge>, usize)
where
    SC: StarkGenericConfig,
    Mat: Matrix<Val<SC>> + Sync,
{
    let quotient_size = quotient_domain.size();
    let width = trace_on_quotient_domain.width();
    let perm_width = permutation_trace_on_quotient_domain.width();
    let mut sels = debug_span!("Compute Selectors")
        .in_scope(|| trace_domain.selectors_on_coset(quotient_domain));

    let qdb = log2_strict_usize(quotient_domain.size()) - log2_strict_usize(trace_domain.size());
    let next_step = 1 << qdb;
    let ext_degree = SC::Challenge::DIMENSION;

    // We take PackedVal::<SC>::WIDTH worth of values at a time from a quotient_size slice, so we need to
    // pad with default values in the case where quotient_size is smaller than PackedVal::<SC>::WIDTH.
    for _ in quotient_size..PackedVal::<SC>::WIDTH {
        sels.is_first_row.push(Val::<SC>::default());
        sels.is_last_row.push(Val::<SC>::default());
        sels.is_transition.push(Val::<SC>::default());
        sels.inv_vanishing.push(Val::<SC>::default());
    }

    let mut alpha_powers = alpha.powers().collect_n(constraint_count);
    alpha_powers.reverse();
    // alpha powers looks like Vec<EF> ~ Vec<[F; D]>
    // It's useful to also have access to the transpose of this of form [Vec<F>; D].
    let decomposed_alpha_powers: Vec<_> = (0..SC::Challenge::DIMENSION)
        .map(|i| {
            alpha_powers
                .iter()
                .map(|x| x.as_basis_coefficients_slice()[i])
                .collect()
        })
        .collect();
    let quotients_and_interaction_counts: Vec<_> = (0..quotient_size)
        .into_par_iter()
        .step_by(PackedVal::<SC>::WIDTH)
        .map(|i_start| {
            let wrap = |i| i % quotient_size;

            let i_range = i_start..i_start + PackedVal::<SC>::WIDTH;

            let is_first_row = *PackedVal::<SC>::from_slice(&sels.is_first_row[i_range.clone()]);
            let is_last_row = *PackedVal::<SC>::from_slice(&sels.is_last_row[i_range.clone()]);
            let is_transition = *PackedVal::<SC>::from_slice(&sels.is_transition[i_range.clone()]);
            let inv_vanishing = *PackedVal::<SC>::from_slice(&sels.inv_vanishing[i_range]);

            let main = RowMajorMatrix::new(
                trace_on_quotient_domain.vertically_packed_row_pair(i_start, next_step),
                width,
            );

            let perm_local: Vec<_> = (0..perm_width)
                .step_by(ext_degree)
                .map(|col| {
                    PackedChallenge::<SC>::from_basis_coefficients_fn(|i| {
                        PackedVal::<SC>::from_fn(|offset| {
                            permutation_trace_on_quotient_domain
                                .get(wrap(i_start + offset), col + i)
                                .unwrap()
                        })
                    })
                })
                .collect();

            let perm_next: Vec<_> = (0..perm_width)
                .step_by(ext_degree)
                .map(|col| {
                    PackedChallenge::<SC>::from_basis_coefficients_fn(|i| {
                        PackedVal::<SC>::from_fn(|offset| {
                            permutation_trace_on_quotient_domain
                                .get(wrap(i_start + next_step + offset), col + i)
                                .unwrap()
                        })
                    })
                })
                .collect();

            let accumulator = PackedChallenge::<SC>::ZERO;
            let mut folder = ProverConstraintFolder {
                main: main.as_view(),
                public_values,
                is_first_row,
                is_last_row,
                is_transition,
                alpha_powers: &alpha_powers,
                decomposed_alpha_powers: &decomposed_alpha_powers,
                accumulator,
                constraint_index: 0,
                perm: VerticalPair::new(
                    RowMajorMatrixView::new_row(&perm_local),
                    RowMajorMatrixView::new_row(&perm_next),
                ),
                perm_challenges,
            };
            let mut folder = LogupInteractionAirBuilder::new(&mut folder);
            air.eval(&mut folder);

            let num_interactions = folder.get_interaction_count();

            // quotient(x) = constraints(x) / Z_H(x)
            let quotient = folder.inner.accumulator * inv_vanishing;

            // "Transpose" D packed base coefficients into WIDTH scalar extension coefficients.
            (
                (0..core::cmp::min(quotient_size, PackedVal::<SC>::WIDTH)).map(
                    move |idx_in_packing| {
                        SC::Challenge::from_basis_coefficients_fn(|coeff_idx| {
                            quotient.as_basis_coefficients_slice()[coeff_idx].as_slice()
                                [idx_in_packing]
                        })
                    },
                ),
                num_interactions,
            )
        })
        .collect();

    let num_interactions = if quotients_and_interaction_counts.is_empty() {
        0
    } else {
        quotients_and_interaction_counts[0].1
    };

    // TODO assert interaction count same across all entries

    let quotients = quotients_and_interaction_counts
        .into_iter()
        .map(|(a, _)| a.collect_vec())
        .flatten()
        .collect_vec();

    (quotients, num_interactions)
}

// #[cfg(test)]
// mod tests {
//     use alloc::vec;
//     use alloc::vec::Vec;

//     use p3_air::*;
//     use p3_air::symbolic_builder::*;
//     use p3_air::symbolic_variable::*;
//     use p3_air::symbolic_expression::*;
//     use p3_baby_bear::BabyBear;

//     use super::*;

//     #[derive(Debug)]
//     struct MockAir {
//         constraints: Vec<SymbolicVariable<BabyBear>>,
//         width: usize,
//     }

//     impl BaseAir<BabyBear> for MockAir {
//         fn width(&self) -> usize {
//             self.width
//         }
//     }

//     impl Air<SymbolicAirBuilder<BabyBear, (), ()>> for MockAir {
//         fn eval(&self, builder: &mut SymbolicAirBuilder<BabyBear, (), ()>) {
//             for constraint in &self.constraints {
//                 builder.assert_zero(*constraint);
//             }
//         }
//     }

//     #[test]
//     fn test_get_log_quotient_degree_no_constraints() {
//         let air = MockAir {
//             constraints: vec![],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);
//         let log_degree = get_log_quotient_degree(&air_box, 3, 2, 0);
//         assert_eq!(log_degree, 0);
//     }

//     #[test]
//     fn test_get_log_quotient_degree_single_constraint() {
//         let air = MockAir {
//             constraints: vec![SymbolicVariable::new(Entry::Main { offset: 0 }, 0)],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);
//         let log_degree = get_log_quotient_degree(&air_box, 3, 2, 0);
//         assert_eq!(log_degree, log2_ceil_usize(1));
//     }

//     #[test]
//     fn test_get_log_quotient_degree_multiple_constraints() {
//         let air = MockAir {
//             constraints: vec![
//                 SymbolicVariable::new(Entry::Main { offset: 0 }, 0),
//                 SymbolicVariable::new(Entry::Main { offset: 1 }, 1),
//                 SymbolicVariable::new(Entry::Main { offset: 2 }, 2),
//             ],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);
//         let log_degree = get_log_quotient_degree(&air_box, 3, 2, 0);
//         assert_eq!(log_degree, log2_ceil_usize(1));
//     }

//     #[test]
//     fn test_get_max_constraint_degree_no_constraints() {
//         let air = MockAir {
//             constraints: vec![],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);
//         let max_degree = get_max_constraint_degree(&air_box, 3, 2);
//         assert_eq!(
//             max_degree, 0,
//             "No constraints should result in a degree of 0"
//         );
//     }

//     #[test]
//     fn test_get_max_constraint_degree_multiple_constraints() {
//         let air = MockAir {
//             constraints: vec![
//                 SymbolicVariable::new(Entry::Main { offset: 0 }, 0),
//                 SymbolicVariable::new(Entry::Main { offset: 1 }, 1),
//                 SymbolicVariable::new(Entry::Main { offset: 2 }, 2),
//             ],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);
//         let max_degree = get_max_constraint_degree(&air_box, 3, 2);
//         assert_eq!(max_degree, 1, "Max constraint degree should be 1");
//     }

//     #[test]
//     fn test_get_symbolic_constraints() {
//         let c1 = SymbolicVariable::new(Entry::Main { offset: 0 }, 0);
//         let c2 = SymbolicVariable::new(Entry::Main { offset: 1 }, 1);

//         let air = MockAir {
//             constraints: vec![c1, c2],
//             width: 4,
//         };
//         let air_box: Box<dyn Air<SymbolicAirBuilder<BabyBear, _, _>>> = Box::new(air);

//         let constraints = get_symbolic_constraints(&air_box, 3, 2);

//         assert_eq!(constraints.len(), 2, "Should return exactly 2 constraints");

//         assert!(
//             constraints.iter().any(|x| matches!(x, SymbolicExpression::Variable(v) if v.index == c1.index && v.entry == c1.entry)),
//             "Expected constraint {:?} was not found",
//             c1
//         );

//         assert!(
//             constraints.iter().any(|x| matches!(x, SymbolicExpression::Variable(v) if v.index == c2.index && v.entry == c2.entry)),
//             "Expected constraint {:?} was not found",
//             c2
//         );
//     }

//     #[test]
//     fn test_symbolic_air_builder_initialization() {
//         let builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);

//         let expected_main = [
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 0),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 1),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 2),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 0 }, 3),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 0),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 1),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 2),
//             SymbolicVariable::<BabyBear>::new(Entry::Main { offset: 1 }, 3),
//         ];

//         let builder_main = builder.main.values;

//         assert_eq!(
//             builder_main.len(),
//             expected_main.len(),
//             "Main matrix should have the expected length"
//         );

//         for (expected, actual) in expected_main.iter().zip(builder_main.iter()) {
//             assert_eq!(expected.index, actual.index, "Index mismatch");
//             assert_eq!(expected.entry, actual.entry, "Entry mismatch");
//         }
//     }

//     #[test]
//     fn test_symbolic_air_builder_is_first_last_row() {
//         let builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);

//         assert!(
//             matches!(builder.is_first_row(), SymbolicExpression::IsFirstRow),
//             "First row condition did not match"
//         );

//         assert!(
//             matches!(builder.is_last_row(), SymbolicExpression::IsLastRow),
//             "Last row condition did not match"
//         );
//     }

//     #[test]
//     fn test_symbolic_air_builder_assert_zero() {
//         let mut builder = SymbolicAirBuilder::<BabyBear, (), ()>::new(2, 4, 3, 0);
//         let expr = SymbolicExpression::Constant(BabyBear::new(5));
//         builder.assert_zero(expr.clone());

//         let constraints = builder.base_constraints();
//         assert_eq!(constraints.len(), 1, "One constraint should be recorded");

//         assert!(
//             constraints.iter().any(
//                 |x| matches!(x, SymbolicExpression::Constant(val) if *val == BabyBear::new(5))
//             ),
//             "Constraint should match the asserted one"
//         );
//     }
// }
