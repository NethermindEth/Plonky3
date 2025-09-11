use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::{Air, ExtensionBuilder};
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
    StarkGenericConfig, SymbolicAirBuilder, SymbolicExpression, Val, get_symbolic_constraints,
};

#[derive(PartialEq)]
enum Loc {
    MulLhs,
    MulRhs,
    AddLhs,
    AddRhs,
    SubLhs,
    SubRhs,
    Neg,
    Top,
}

fn symbolic_expression_to_string<F>(expression: &SymbolicExpression<F>, loc: Loc) -> String
where
    F: std::fmt::Debug,
{
    match expression {
        SymbolicExpression::Variable(symbolic_variable) => format!(
            "{}[{}]",
            match symbolic_variable.entry {
                crate::Entry::Preprocessed { offset } => format!("Preprocessed{offset}"),
                crate::Entry::Main { offset } => format!("Main{offset}"),
                crate::Entry::Permutation { offset } => format!("Permutation{offset}"),
                crate::Entry::Public => format!("Public"),
                crate::Entry::Challenge => format!("Challenge"),
            },
            symbolic_variable.index
        ),
        SymbolicExpression::IsFirstRow => "IsFirstRow".to_string(),
        SymbolicExpression::IsLastRow => "IsLastRow".to_string(),
        SymbolicExpression::IsTransition => "IsTransition".to_string(),
        SymbolicExpression::Constant(x) => format!("constant{x:?}"),
        SymbolicExpression::Add {
            x,
            y,
            degree_multiple: _,
        } => {
            if loc == Loc::MulLhs || loc == Loc::MulRhs || loc == Loc::Neg {
                format!(
                    "({} + {})",
                    symbolic_expression_to_string(x, Loc::AddLhs),
                    symbolic_expression_to_string(y, Loc::AddRhs),
                )
            } else if loc == Loc::SubRhs {
                format!(
                    "{} - {}",
                    symbolic_expression_to_string(x, Loc::SubLhs),
                    symbolic_expression_to_string(y, Loc::SubRhs),
                )
            } else {
                format!(
                    "{} + {}",
                    symbolic_expression_to_string(x, Loc::AddLhs),
                    symbolic_expression_to_string(y, Loc::AddRhs),
                )
            }
        }
        SymbolicExpression::Sub {
            x,
            y,
            degree_multiple: _,
        } => {
            if loc == Loc::AddLhs || loc == Loc::AddRhs || loc == Loc::Top {
                format!(
                    "{} - {}",
                    symbolic_expression_to_string(x, Loc::SubLhs),
                    symbolic_expression_to_string(y, Loc::SubRhs),
                )
            } else {
                format!(
                    "({} - {})",
                    symbolic_expression_to_string(x, Loc::SubLhs),
                    symbolic_expression_to_string(y, Loc::SubRhs),
                )
            }
        }
        SymbolicExpression::Neg {
            x,
            degree_multiple: _,
        } => {
            format!("-{}", symbolic_expression_to_string(x, Loc::Neg))
        }
        SymbolicExpression::Mul {
            x,
            y,
            degree_multiple: _,
        } => {
            format!(
                "{} * {}",
                symbolic_expression_to_string(x, Loc::MulLhs),
                symbolic_expression_to_string(y, Loc::MulRhs)
            )
        }
    }
}

#[instrument(skip_all)]
#[allow(clippy::multiple_bound_locations)] // cfg not supported in where clauses?
pub fn prove<
    SC,
    #[cfg(debug_assertions)] A: for<'a> Air<crate::check_constraints::DebugConstraintBuilder<'a, Val<SC>>>,
    #[cfg(not(debug_assertions))] A,
>(
    config: &SC,
    air: &A,
    trace: RowMajorMatrix<Val<SC>>,
    permutation_trace: RowMajorMatrix<Val<SC>>,
    public_values: &Vec<Val<SC>>,
) -> Proof<SC>
where
    SC: StarkGenericConfig,
    A: Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<ProverConstraintFolder<'a, SC>>,
{
    #[cfg(debug_assertions)]
    crate::check_constraints::check_constraints(air, &trace, public_values);

    let pcs = config.pcs();

    let degree = trace.height();
    let log_degree = log2_strict_usize(degree);
    let log_ext_degree = log_degree + config.is_zk();

    let symbolic_constraints = get_symbolic_constraints::<Val<SC>, A>(air, 0, public_values.len());
    for (idx, constraint) in symbolic_constraints.iter().enumerate() {
        println!(
            "{idx}: {} = 0\n",
            symbolic_expression_to_string(constraint, Loc::Top)
        );
    }
    let constraint_count = symbolic_constraints.len();
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

    let (trace_commit, trace_data) =
        info_span!("commit to trace data").in_scope(|| pcs.commit([(ext_trace_domain, trace)]));

    // Observe the instance.
    // degree < 2^255 so we can safely cast log_degree to a u8.
    challenger.observe(Val::<SC>::from_u8(log_ext_degree as u8));
    challenger.observe(Val::<SC>::from_u8(log_degree as u8));
    // TODO: Might be best practice to include other instance data here; see verifier comment.

    challenger.observe(trace_commit.clone());
    challenger.observe_slice(public_values);

    let permutation_trace = permutation_trace.flatten_to_base();
    let (permutation_commit, permutation_data) = pcs.commit([(trace_domain, permutation_trace)]);

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

    let trace_on_quotient_domain = pcs.get_evaluations_on_domain(&trace_data, 0, quotient_domain);
    let permutation_trace_on_quotient_domain =
        pcs.get_evaluations_on_domain(&permutation_data, 0, quotient_domain);

    let perm_challenges = (0..2)
        .map(|_| challenger.sample_algebra_element::<SC::Challenge>().into())
        .collect::<Vec<PackedChallenge<SC>>>();

    let quotient_values = quotient_values(
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

    let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();
    let quotient_chunks = quotient_domain.split_evals(quotient_degree, quotient_flat);
    let qc_domains = quotient_domain.split_domains(quotient_degree);

    let (quotient_commit, quotient_data) = info_span!("commit to quotient poly chunks")
        .in_scope(|| pcs.commit_quotient(qc_domains, quotient_chunks));
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
    let trace_local = opened_values[trace_idx][0][0].clone();
    let trace_next = opened_values[trace_idx][0][1].clone();
    let permutation_trace_local = opened_values[trace_idx][2][0].clone();
    let permutation_trace_next = opened_values[trace_idx][2][1].clone();
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
    Proof {
        commitments,
        opened_values,
        opening_proof,
        degree_bits: log_ext_degree,
    }
}

#[instrument(name = "compute quotient polynomial", skip_all)]
// TODO: Group some arguments to remove the `allow`?
#[allow(clippy::too_many_arguments)]
fn quotient_values<SC, A, Mat>(
    air: &A,
    public_values: &Vec<Val<SC>>,
    trace_domain: Domain<SC>,
    quotient_domain: Domain<SC>,
    trace_on_quotient_domain: Mat,
    permutation_trace_on_quotient_domain: Mat,
    alpha: SC::Challenge,
    perm_challenges: &[PackedChallenge<SC>],
    constraint_count: usize,
) -> Vec<SC::Challenge>
where
    SC: StarkGenericConfig,
    A: for<'a> Air<ProverConstraintFolder<'a, SC>>,
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

    let mut alpha_powers = alpha.powers().take(constraint_count).collect_vec();
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
    (0..quotient_size)
        .into_par_iter()
        .step_by(PackedVal::<SC>::WIDTH)
        .flat_map_iter(|i_start| {
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
            air.eval(&mut folder);

            // quotient(x) = constraints(x) / Z_H(x)
            let quotient = folder.accumulator * inv_vanishing;

            // "Transpose" D packed base coefficients into WIDTH scalar extension coefficients.
            (0..core::cmp::min(quotient_size, PackedVal::<SC>::WIDTH)).map(move |idx_in_packing| {
                SC::Challenge::from_basis_coefficients_fn(|coeff_idx| {
                    quotient.as_basis_coefficients_slice()[coeff_idx].as_slice()[idx_in_packing]
                })
            })
        })
        .collect()
}
