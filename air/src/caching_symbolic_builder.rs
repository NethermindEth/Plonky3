use std::sync::{Arc, Mutex};

use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_field::{Algebra, ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;

use crate::cached_symbolic_expression::{CacheExpression, CacheSymbolicExpression, CacheSymbolicVariable, CacheVar, CopySymbolicVariable, SymbolicCache, cache_symbolic_expression_to_lean, merge_into_cache, symbolic_cache_to_lean};
use crate::{
    AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, InteractionAirBuilder, PairBuilder,
    PermutationAirBuilder,
};

fn indent(code: String, indentation: &str) -> String {
    code.split("\n").map(|line| format!("{indentation}{line}")).join("\n")
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
pub struct CachingSymbolicAirBuilder<F, EF> {
    preprocessed: RowMajorMatrix<CacheSymbolicVariable<F>>,
    main: RowMajorMatrix<CacheSymbolicVariable<F>>,
    permutation: RowMajorMatrix<CopySymbolicVariable>,
    public_values: Vec<CopySymbolicVariable>,
    challenges: Vec<CopySymbolicVariable>,
    base_constraints: Vec<CacheSymbolicExpression<F>>,
    extension_constraints: Vec<CacheSymbolicExpression<EF>>,
    interactions: Vec<Interaction<CacheSymbolicExpression<F>>>,
}

impl<F, EF> CachingSymbolicAirBuilder<F, EF>
where
    F: Clone + Send + Sync,
    EF: Clone + Send + Sync,
{
    pub fn new(
        preprocessed_width: usize,
        width: usize,
        permutation_width: usize,
        num_public_values: usize,
        num_challenges: usize,
    ) -> Self {
        let main_cache = Arc::new(Mutex::new(SymbolicCache(Vec::new())));

        {
            let mut main_cache = main_cache.lock().unwrap();
            
            main_cache.0.push(CacheExpression::Var(CacheVar::IsFirstRow));
            main_cache.0.push(CacheExpression::Var(CacheVar::IsLastRow));
            main_cache.0.push(CacheExpression::Var(CacheVar::IsTransition));
            
            for rotation in [0, 1] {
                for preprocessed_idx in 0..preprocessed_width {
                    main_cache.0.push(CacheExpression::Var(CacheVar::Preprocessed { index: preprocessed_idx, offset: rotation }));
                }

                for main_idx in 0..width {
                    main_cache.0.push(CacheExpression::Var(CacheVar::Main { index: main_idx, offset: rotation }));
                }
            
            }
        };
        let (prep_values, main_values, permutation_values, public_values, challenges) = {
            let mut main_idx = 2;

            let mut prep_values = vec![];
            let mut main_values = vec![];
            let mut permutation_values = vec![];
            let mut public_values = vec![];
            let mut challenges = vec![];
            
            for rotation in [0, 1] {
                for _ in 0..preprocessed_width {
                    main_idx += 1;
                    prep_values.push(CacheSymbolicVariable{idx: main_idx, cache: main_cache.clone()});
                }

                for _ in 0..width {
                    main_idx += 1;
                    main_values.push(CacheSymbolicVariable{idx: main_idx, cache: main_cache.clone()});
                }
                
                for permutation_idx in 0..permutation_width {
                    permutation_values.push(CopySymbolicVariable::Permutation{idx: permutation_idx, offset: rotation});
                }
            }
            
            for public_idx in 0..num_public_values {
                public_values.push(CopySymbolicVariable::Public{idx: main_idx});
            }
            
            for challenge_idx in 0..num_challenges {
                challenges.push(CopySymbolicVariable::Challenge{idx: challenge_idx});
            }

            (prep_values, main_values, permutation_values, public_values, challenges)
        };

        Self {
            preprocessed: RowMajorMatrix::new(prep_values, preprocessed_width),
            main: RowMajorMatrix::new(main_values, width),
            permutation: RowMajorMatrix::new(permutation_values, permutation_width),
            public_values,
            challenges,
            base_constraints: vec![],
            extension_constraints: vec![],
            interactions: vec![]
        }
    }

    pub fn base_constraints(&self) -> &Vec<CacheSymbolicExpression<F>> {
        &(self.base_constraints)
    }

    pub fn extension_constraints(&self) -> &Vec<CacheSymbolicExpression<EF>> {
        &(self.extension_constraints)
    }

    pub fn interactions(&self) -> &Vec<Interaction<CacheSymbolicExpression<F>>> {
        &(self.interactions)
    }
}

impl<F, EF> CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
    EF: Field,
{
    fn print_lean_base_constraints(&self) {
        println!("--Base constraints---");

        let mut cache: Option<Arc<Mutex<SymbolicCache<F>>>> = None;

        let constraints = self.base_constraints
            .iter()
            .enumerate()
            .map(|(idx, constraint)| {
                // println!("Merging {idx}");
                match constraint {
                    CacheSymbolicExpression::Variable(var) => {
                        match cache.clone() {
                            Some(cache) => {
                                let idx = merge_into_cache(cache.clone(), &var);
                                CacheSymbolicExpression::Variable(CacheSymbolicVariable { idx, cache: cache.clone() })
                            },
                            None => {
                                cache = Some(var.cache.clone());
                                CacheSymbolicExpression::Variable(var.clone())
                            },
                        }
                    },
                    CacheSymbolicExpression::Constant(cache_symbolic_constant) => {
                        CacheSymbolicExpression::Constant(cache_symbolic_constant.clone())
                    },
                }
            })
            .collect_vec();

        match cache {
            Some(cache) => {
                let cache = &cache.lock().unwrap();
                // println!("Printing {} subexpressions", cache.0.len());
                println!("{}", symbolic_cache_to_lean(cache, "F"));
            },
            None => println!("No subexpressions to print"),
        }

        for (idx, constraint) in constraints
            .iter()
            .enumerate()
        {
            println!(
                "def constraint_{idx} {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n  {} = 0",
                cache_symbolic_expression_to_lean(constraint)
            );
        }
    }

    fn print_lean_extension_field_constraints_warning(&self) {
        if !self.extension_constraints.is_empty() {
            println!("-- WARNING: extension field constraints are not currently printed");
        }
    }

    // fn print_lean_interactions(&self) {
    //     let interactions_text = self
    //         .interactions
    //         .iter()
    //         .map(|interaction| {
    //             let multiplicity =
    //                 symbolic_expression_to_lean_string(&interaction.multiplicity, None);
    //             let data = format!(
    //                 "[{}]",
    //                 interaction
    //                     .data
    //                     .iter()
    //                     .map(|x| symbolic_expression_to_lean_string(x, None))
    //                     .join(", ")
    //             );
    //             format!("({multiplicity}, {data})")
    //         })
    //         .join(", ");

    //     println!("  @[simp]");
    //     println!(
    //         "  def constrain_interactions {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :="
    //     );
    //     println!(
    //         "    Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [{interactions_text}])"
    //     );
    // }

    fn simplification_proof() -> String {
        [
            "apply Iff.intro",
            ". intro h",
            "  simp [plonky3_encapsulation, NAME_constraint_and_interaction_simplification] at h",
            "  simp only [NAME_constraint_and_interaction_simplification]",
            "  exact h",
            ". intro h",
            "  simp [plonky3_encapsulation, NAME_constraint_and_interaction_simplification]",
            "  simp only [NAME_constraint_and_interaction_simplification] at h",
            "  exact h",
        ]
        .join("\n")
    }

    // fn print_lean_constraint_simplification(&self) {
    //     println!("-----Constraint simplification------");
    //     for (idx, constraint) in self.base_constraints.iter().enumerate() {
    //         let constraint_text = format!(
    //             "{}",
    //             symbolic_expression_to_lean_string(constraint, None)
    //         );

    //         let simplified_constraint_text = [
    //             format!("@[NAME_constraint_and_interaction_simplification]"),
    //             format!("def constraint_{idx} (air : Valid_NAME F ExtF) (row : ℕ) : Prop :="),
    //             format!("  sorry"),
    //         ]
    //         .join("\n");

    //         let simplified_of_extracted = [
    //             format!("@[NAME_air_simplification]"),
    //             format!("lemma constraint_{idx}_of_extraction"),
    //             format!("    (air : Valid_NAME F ExtF) (row : ℕ)"),
    //             format!(
    //                 ": NAME.extraction.constraint_{idx} air row ↔ constraint_{idx} air row := by"
    //             ),
    //             Self::simplification_proof(),
    //         ]
    //         .join("\n");

    //         let output_text = format!("{simplified_constraint_text}\n\n{simplified_of_extracted}");

    //         if constraint_text.contains("Circuit.permutation") {
    //             let commented = output_text
    //                 .split("\n")
    //                 .map(|line| format!("-- {line}"))
    //                 .join("\n");
    //             println!("{commented}\n");
    //         } else {
    //             println!("{output_text}\n");
    //         }
    //     }
    // }

    fn print_lean_interaction_simplification(&self) {
        println!("-----Interaction simplification-----");
        {
            let simplified_constraint_text = [
                format!("@[NAME_constraint_and_interaction_simplification]"),
                format!("def constrain_interactions (air : Valid_NAME F ExtF) : Prop :="),
                format!("  sorry"),
            ]
            .join("\n");

            let simplified_of_extracted = [
                format!("@[NAME_air_simplification]"),
                format!("lemma constrain_interactions_of_extraction"),
                format!("    (air : Valid_NAME F ExtF)"),
                format!(": NAME.extraction.constrain_interactions air ↔ constrain_interactions air := by"),
                Self::simplification_proof()
            ].join("\n");

            let output_text = format!("{simplified_constraint_text}\n\n{simplified_of_extracted}");

            println!("{output_text}\n");
        }
    }

    fn print_lean_all_hold(&self) {
        println!("-----All hold definitions-----------");

        let num_constraints = self.base_constraints.len();

        let extracted_row_constraint_list = (0..num_constraints)
            .map(|idx| format!("    NAME.extraction.constraint_{idx} air row,"))
            .join("\n");

        let extract_row_constraint_list_def = [
            format!("@[simp]"),
            format!("def extracted_row_constraint_list"),
            format!("  [Field ExtF]"),
            format!("  (air : Valid_NAME FBB ExtF)"),
            format!("  (row : ℕ)"),
            format!(": List Prop :="),
            format!("  ["),
            extracted_row_constraint_list,
            format!("  ]"),
        ]
        .join("\n");

        let all_hold_def = [
            "@[simp]",
            "def allHold",
            "  [Field ExtF]",
            "  (air : Valid_NAME FBB ExtF)",
            "  (row : ℕ)",
            "  (_ : row ≤ air.last_row)",
            ": Prop :=",
            "  NAME.extraction.constrain_interactions air ∧",
            "  List.Forall (·) (extracted_row_constraint_list air row)",
        ]
        .join("\n");

        let row_constraint_list = (0..num_constraints)
            .map(|idx| format!("    constraint_{idx} air row,"))
            .join("\n");

        let row_constraint_list_def = [
            format!("@[simp]"),
            format!("def row_constraint_list"),
            format!("  [Field ExtF]"),
            format!("  (air : Valid_NAME FBB ExtF)"),
            format!("  (row : ℕ)"),
            format!(": List Prop :="),
            format!("  ["),
            row_constraint_list,
            format!("  ]"),
        ]
        .join("\n");

        let all_hold_simplified = [
            "@[simp]",
            "def allHold_simplified",
            "  [Field ExtF]",
            "  (air : Valid_NAME FBB ExtF)",
            "  (row : ℕ)",
            "  (_ : row ≤ air.last_row)",
            ": Prop :=",
            "  constrain_interactions air ∧",
            "  List.Forall (·) (row_constraint_list air row)",
        ]
        .join("\n");

        let all_hold_simplified_of_all_hold = [
            "lemma allHold_simplified_of_allHold",
            "  [Field ExtF]",
            "  (air : Valid_NAME FBB ExtF)",
            "  (row : ℕ)",
            "  (h_row : row ≤ air.last_row)",
            ": allHold air row h_row ↔ allHold_simplified air row h_row := by",
            "  unfold allHold allHold_simplified",
            "  apply Iff.and",
            "  . unfold NAME.extraction.constrain_interactions",
            "    simp [plonky3_encapsulation]",
            "    rfl",
            "  . simp only [extracted_row_constraint_list,",
            "              row_constraint_list,",
            "              NAME_air_simplification]",
        ]
        .join("\n");

        let all_hold_section = [
            extract_row_constraint_list_def,
            all_hold_def,
            row_constraint_list_def,
            all_hold_simplified,
            all_hold_simplified_of_all_hold,
        ]
        .join("\n\n");

        println!("{all_hold_section}");
    }

    pub fn print_lean_constraints(&self) {
        println!("Num constraints: {}", self.base_constraints.len());
        self.print_lean_base_constraints();
        // self.print_lean_extension_field_constraints_warning();
        // self.print_lean_interactions();

        // self.print_lean_constraint_simplification();
        // self.print_lean_interaction_simplification();

        // self.print_lean_all_hold();
        println!("------");
    }
}

impl<F, EF> AirBuilder for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
{
    type F = F;
    type Expr = CacheSymbolicExpression<F>;
    type Var = CacheSymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        CacheSymbolicExpression::Variable(CacheSymbolicVariable{
            idx: 0,
            cache: Arc::new(Mutex::new(SymbolicCache(Vec::new())))
        })
    }

    fn is_last_row(&self) -> Self::Expr {
        CacheSymbolicExpression::Variable(CacheSymbolicVariable{
            idx: 1,
            cache: Arc::new(Mutex::new(SymbolicCache(Vec::new())))
        })
    }

    /// # Panics
    /// This function panics if `size` is not `2`.
    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            CacheSymbolicExpression::Variable(CacheSymbolicVariable{
            idx: 2,
            cache: Arc::new(Mutex::new(SymbolicCache(Vec::new())))
        })
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.base_constraints.push(x.into());
    }
}

impl<F, EF> AirBuilderWithPublicValues for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
{
    type PublicVar = CopySymbolicVariable;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F, EF> PairBuilder for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
{
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F, EF> ExtensionBuilder for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
    EF: ExtensionField<F>,
    CacheSymbolicExpression<EF>: Algebra<CacheSymbolicExpression<F>>,
{
    type EF = EF;

    type ExprEF = CacheSymbolicExpression<EF>;

    type VarEF = CopySymbolicVariable;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.extension_constraints.push(x.into())
    }
}

impl<F, EF> PermutationAirBuilder for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
    EF: ExtensionField<F>,
    CacheSymbolicExpression<EF>: Algebra<CacheSymbolicExpression<F>>,
{
    type MP = RowMajorMatrix<Self::VarEF>;

    type RandomVar = CopySymbolicVariable;

    fn permutation(&self) -> Self::MP {
        self.permutation.clone()
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        self.challenges.as_slice()
    }
}

impl<F, EF> InteractionAirBuilder for CachingSymbolicAirBuilder<F, EF>
where
    F: Field,
{
    fn register_interaction<Data: Iterator<Item: Into<Self::Expr>>, Count: Into<Self::Expr>>(
        &mut self,
        data: Data,
        count: Count,
    ) {
        self.interactions.push(Interaction {
            data: data.map(|x| x.into()).collect(),
            multiplicity: count.into(),
        });
    }
}
