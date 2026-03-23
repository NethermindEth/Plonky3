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
                public_values.push(CopySymbolicVariable::Public{idx: public_idx});
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
            .map(|constraint| {
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

    pub fn print_lean_constraints(&self) {
        println!("Num constraints: {}", self.base_constraints.len());
        self.print_lean_base_constraints();
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
