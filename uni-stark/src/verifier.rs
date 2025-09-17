//! See `prover.rs` for an overview of the protocol and a more detailed soundness analysis.

use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_air::{logup::LogupInteractionAirBuilder, Air, BaseAir};
use p3_challenger::{CanObserve, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use p3_util::zip_eq::zip_eq;
use tracing::instrument;

use crate::{get_log_quotient_degree, LogupAir, PcsError, Proof, StarkGenericConfig, Val, VerifierConstraintFolder};

#[instrument(skip_all)]
pub fn verify<SC>(
    config: &SC,
    airs: &Vec<Box<dyn LogupAir<SC>>>,
    proofs: &Vec<Proof<SC>>,
    cumulative_sums: &Vec<<SC as StarkGenericConfig>::Challenge>,
    public_values: &Vec<Vec<Val<SC>>>,
) -> Result<(), VerificationError<PcsError<SC>>>
where
    SC: StarkGenericConfig,
{
    let sum = cumulative_sums
        .iter()
        .fold(<SC as StarkGenericConfig>::Challenge::ZERO, |acc, x| acc + *x);

    if sum != <SC as StarkGenericConfig>::Challenge::ZERO {
        return Err(VerificationError::LogupSumFailed);
    }

    for i in 0..airs.len() {
        let air = &airs[i];
        let proof = &proofs[i];
        let cumulative_sum = cumulative_sums[i];
        let public_values = &public_values[i];
        let Proof {
            commitments,
            opened_values,
            opening_proof,
            degree_bits,
        } = proof;
    
        let pcs = config.pcs();
    
        let degree = 1 << degree_bits;
        let log_quotient_degree =
            get_log_quotient_degree(air, 0, public_values.len(), config.is_zk());
        let quotient_degree = 1 << (log_quotient_degree + config.is_zk());
    
        let mut challenger = config.initialise_challenger();
        let trace_domain = pcs.natural_domain_for_degree(degree);
        let init_trace_domain = pcs.natural_domain_for_degree(degree >> (config.is_zk()));
    
        let quotient_domain =
            trace_domain.create_disjoint_domain(1 << (degree_bits + log_quotient_degree));
        let quotient_chunks_domains = quotient_domain.split_domains(quotient_degree);
    
        let trace_domains = quotient_chunks_domains
            .iter()
            .map(|domain| pcs.natural_domain_for_degree(domain.size() << (config.is_zk())))
            .collect_vec();
    
        // Check that the random commitments are/are not present depending on the ZK setting.
        if SC::Pcs::ZK {
            // If ZK is enabled, the prover should have random commitments.
            if opened_values.random.is_none() || commitments.random.is_none() {
                return Err(VerificationError::RandomizationError);
            }
            // If ZK is not enabled, the prover should not have random commitments.
        } else if opened_values.random.is_some() || commitments.random.is_some() {
            return Err(VerificationError::RandomizationError);
        }
    
        let air_width = <dyn LogupAir<SC> as BaseAir<Val<SC>>>::width(air.as_ref());
        let valid_shape = opened_values.trace_local.len() == air_width
            && opened_values.trace_next.len() == air_width
            && opened_values.quotient_chunks.len() == quotient_degree
            && opened_values
                .quotient_chunks
                .iter()
                .all(|qc| qc.len() == <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION)
            // We've already checked that opened_values.random is present if and only if ZK is enabled.
            && if let Some(r_comm) = &opened_values.random {
                r_comm.len() == SC::Challenge::DIMENSION
            } else {
                true
            };
        if !valid_shape {
            return Err(VerificationError::InvalidProofShape);
        }
    
        // Observe the instance.
        challenger.observe(Val::<SC>::from_usize(proof.degree_bits));
        challenger.observe(Val::<SC>::from_usize(proof.degree_bits - config.is_zk()));
        // TODO: Might be best practice to include other instance data here in the transcript, like some
        // encoding of the AIR. This protects against transcript collisions between distinct instances.
        // Practically speaking though, the only related known attack is from failing to include public
        // values. It's not clear if failing to include other instance data could enable a transcript
        // collision, since most such changes would completely change the set of satisfying witnesses.
    
        challenger.observe(commitments.trace.clone());
        challenger.observe_slice(public_values);
    
        challenger.observe(commitments.permutation_trace.clone());
    
        let perm_challenges = (0..2)
            .map(|_| challenger.sample_algebra_element::<SC::Challenge>())
            .collect::<Vec<SC::Challenge>>();
    
        // Get the first Fiat Shamir challenge which will be used to combine all constraint polynomials
        // into a single polynomial.
        //
        // Soundness Error: n/|EF| where n is the number of constraints.
        let alpha: SC::Challenge = challenger.sample_algebra_element();
    
        challenger.observe_slice(&<SC as StarkGenericConfig>::Challenge::flatten_to_base(vec![cumulative_sum]));

        challenger.observe(commitments.quotient_chunks.clone());
    
        // We've already checked that commitments.random is present if and only if ZK is enabled.
        // Observe the random commitment if it is present.
        if let Some(r_commit) = commitments.random.clone() {
            challenger.observe(r_commit);
        }
    
        // Get an out-of-domain point to open our values at.
        //
        // Soundness Error: dN/|EF| where `N` is the trace length and our constraint polynomial has degree `d`.
        let zeta: SC::Challenge = challenger.sample_algebra_element();
        let zeta_next = init_trace_domain.next_point(zeta).unwrap();
    
        // We've already checked that commitments.random and opened_values.random are present if and only if ZK is enabled.
        let mut coms_to_verify = if let Some(random_commit) = &commitments.random {
            let random_values = opened_values
                .random
                .as_ref()
                .ok_or(VerificationError::RandomizationError)?;
            vec![(
                random_commit.clone(),
                vec![(trace_domain, vec![(zeta, random_values.clone())])],
            )]
        } else {
            vec![]
        };
        coms_to_verify.extend(vec![
            (
                commitments.trace.clone(),
                vec![(
                    trace_domain,
                    vec![
                        (zeta, opened_values.trace_local.clone()),
                        (zeta_next, opened_values.trace_next.clone()),
                    ],
                )],
            ),
            (
                commitments.quotient_chunks.clone(),
                // Check the commitment on the randomized domains.
                zip_eq(
                    trace_domains.iter(),
                    &opened_values.quotient_chunks,
                    VerificationError::InvalidProofShape,
                )?
                .map(|(domain, values)| (*domain, vec![(zeta, values.clone())]))
                .collect_vec(),
            ),
            (
                commitments.trace.clone(),
                vec![(
                    trace_domain,
                    vec![
                        (zeta, opened_values.permutation_trace_local.clone()),
                        (zeta_next, opened_values.permutation_trace_next.clone()),
                    ],
                )],
            ),
        ]);
    
        pcs.verify(coms_to_verify, opening_proof, &mut challenger)
            .map_err(VerificationError::InvalidOpeningArgument)?;
    
        let zps = quotient_chunks_domains
            .iter()
            .enumerate()
            .map(|(i, domain)| {
                quotient_chunks_domains
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, other_domain)| {
                        other_domain.vanishing_poly_at_point(zeta)
                            * other_domain
                                .vanishing_poly_at_point(domain.first_point())
                                .inverse()
                    })
                    .product::<SC::Challenge>()
            })
            .collect_vec();
    
        let quotient = opened_values
            .quotient_chunks
            .iter()
            .enumerate()
            .map(|(ch_i, ch)| {
                // We checked in valid_shape the length of "ch" is equal to
                // <SC::Challenge as BasedVectorSpace<Val<SC>>>::DIMENSION. Hence
                // the unwrap() will never panic.
                zps[ch_i]
                    * ch.iter()
                        .enumerate()
                        .map(|(e_i, &c)| SC::Challenge::ith_basis_element(e_i).unwrap() * c)
                        .sum::<SC::Challenge>()
            })
            .sum::<SC::Challenge>();
    
        let sels = init_trace_domain.selectors_at_point(zeta);
    
        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(&opened_values.trace_local),
            RowMajorMatrixView::new_row(&opened_values.trace_next),
        );
    
        let perm = VerticalPair::new(
            RowMajorMatrixView::new_row(&opened_values.permutation_trace_local),
            RowMajorMatrixView::new_row(&opened_values.permutation_trace_next),
        );
    
        let mut folder = VerifierConstraintFolder {
            main,
            public_values,
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
            alpha,
            accumulator: SC::Challenge::ZERO,
            perm,
            perm_challenges: &perm_challenges,
        };
        let mut folder = LogupInteractionAirBuilder::new(&mut folder);
        air.eval(&mut folder);
        let folded_constraints = folder.inner.accumulator;
    
        // Finally, check that
        //     folded_constraints(zeta) / Z_H(zeta) = quotient(zeta)
        if folded_constraints * sels.inv_vanishing != quotient {
            return Err(VerificationError::OodEvaluationMismatch);
        }
    }

    Ok(())
}

#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    InvalidProofShape,
    /// An error occurred while verifying the claimed openings.
    InvalidOpeningArgument(PcsErr),
    /// Out-of-domain evaluation mismatch, i.e. `constraints(zeta)` did not match
    /// `quotient(zeta) Z_H(zeta)`.
    OodEvaluationMismatch,
    /// The FRI batch randomization does not correspond to the ZK setting.
    RandomizationError,
    LogupSumFailed,
}
