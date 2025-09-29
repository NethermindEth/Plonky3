use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;

use p3_field::{Algebra, ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;

use crate::{AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, InteractionAirBuilder, PairBuilder, PermutationAirBuilder};
use crate::symbolic_variable::Entry;
use crate::symbolic_expression::{symbolic_expression_to_string, SymbolicExpression};
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

impl<F, EF, Challenge> SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: Field
{
    fn print_lean_base_constraints(&self) {
        println!("--Base constraints---");
        for (idx, constraint) in self.base_constraints.iter().enumerate() {
            let constraint_text = format!(
                "  @[simp]\n  def constraint_{idx} {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n    {} = 0\n",
                symbolic_expression_to_string(constraint, "", None)
            );
    
            println!("{constraint_text}");
        }
    }

    fn print_lean_extension_field_constraints_warning(&self) {
        if !self.extension_constraints.is_empty() {
            println!("-- WARNING: extension field constraints are not currently printed");
        }
    }

    fn print_lean_interactions(&self) {
        let interactions_text = self
            .interactions
            .iter()
            .map(|interaction| {
                let multiplicity = symbolic_expression_to_string(
                        &interaction.multiplicity,
                        "",
                        None
                    );
                    let data = format!(
                        "[{}]",
                        interaction
                            .data
                            .iter()
                            .map(|x| symbolic_expression_to_string(x, "", None))
                            .join(", ")
                    );
                    format!("({multiplicity}, {data})")
            })
            .join(", ");

        println!("  @[simp]");
        println!("  def constrain_interactions {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :=");
        println!("    Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [{interactions_text}])");
    }

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
        ].join("\n")
    }

    fn print_lean_constraint_simplification(&self) {
        println!("-----Constraint simplification------");
        for (idx, constraint) in self.base_constraints.iter().enumerate() {
            let constraint_text = format!(
                "{}",
                symbolic_expression_to_string(constraint, "", None)
            );
    
            let simplified_constraint_text = [
                format!("@[NAME_constraint_and_interaction_simplification]"),
                format!("def constraint_{idx} (air : Valid_NAME F ExtF) (row : ℕ) : Prop :="),
                format!("  sorry")
            ].join("\n");
    
            let simplified_of_extracted = [
                format!("@[NAME_air_simplification]"),
                format!("lemma constraint_{idx}_of_extraction"),
                format!("    (air : Valid_NAME F ExtF) (row : ℕ)"),
                format!(": NAME.extraction.constraint_{idx} air row ↔ constraint_{idx} air row := by"),
                Self::simplification_proof()
            ].join("\n");
    
            let output_text = format!(
                "{simplified_constraint_text}\n\n{simplified_of_extracted}"
            );
    
            if constraint_text.contains("Circuit.permutation") {
                let commented = output_text
                    .split("\n")
                    .map(|line| format!("-- {line}"))
                    .join("\n");
                println!("{commented}\n");
            } else {
                println!("{output_text}\n");
            }
        }
    }

    fn print_lean_interaction_simplification(&self) {
        println!("-----Interaction simplification-----");
        {
            let simplified_constraint_text = [
                format!("@[NAME_constraint_and_interaction_simplification]"),
                format!("def constrain_interactions (air : Valid_NAME F ExtF) : Prop :="),
                format!("  sorry")
            ].join("\n");
    
            let simplified_of_extracted = [
                format!("@[NAME_air_simplification]"),
                format!("lemma constrain_interactions_of_extraction"),
                format!("    (air : Valid_NAME F ExtF)"),
                format!(": NAME.extraction.constrain_interactions air ↔ constrain_interactions air := by"),
                Self::simplification_proof()
            ].join("\n");
    
            let output_text = format!(
                "{simplified_constraint_text}\n\n{simplified_of_extracted}"
            );
    
            println!("{output_text}\n");
        }
    }

    fn print_lean_all_hold(&self) {
        println!("-----All hold definitions-----------");
    
        let num_constraints = self.base_constraints.len();
    
        let extracted_row_constraint_list = (0..num_constraints)
            .map(|idx| {
                format!("    NAME.extraction.constraint_{idx} air row,")
            })
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
        ].join("\n");
    
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
        ].join("\n");
    
        let row_constraint_list = (0..num_constraints)
            .map(|idx| {
                format!("    constraint_{idx} air row,")
            })
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
        ].join("\n");
    
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
        ].join("\n");
    
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
        ].join("\n");
    
        let all_hold_section = [
            extract_row_constraint_list_def,
            all_hold_def,
            row_constraint_list_def,
            all_hold_simplified,
            all_hold_simplified_of_all_hold
        ].join("\n\n");
    
        println!("{all_hold_section}");
    }

    pub fn print_lean_constraints(&self) {
        self.print_lean_base_constraints();
        self.print_lean_extension_field_constraints_warning();
        self.print_lean_interactions();

        self.print_lean_constraint_simplification();
        self.print_lean_interaction_simplification();
        
        self.print_lean_all_hold();
        println!("------");
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
