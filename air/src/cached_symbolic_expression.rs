use itertools::Itertools;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::fmt::Display;
use std::sync::{Arc, Mutex};

use p3_field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

// Var must be convertible to expression
// Var must be thread safe
// F must be convertible to Expr
// Expressions including Vars must reference the Cache
// Expressions that are only constants cannot reference the Cache
// Expressions that are only vars contain only data in the var
// Vars must store the reference to the cache
// Cache contains unique expressions
//  Leaves
//    No Constants
//    Enum trace type
//    Index
//    Offset as necessary
//  Negation
//    Cache Index of operand
//  Binary operations
//    Opcode
//    Cache indices of operands
//  Immediate Variations

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CacheVar {
    Preprocessed { index: usize, offset: usize },
    Main { index: usize, offset: usize },
    Permutation { index: usize, offset: usize },
    Public(usize),
    Challenge(usize),
    IsFirstRow,
    IsLastRow,
    IsTransition
}

fn cache_var_to_lean(x: CacheVar) -> String {
    match x {
        CacheVar::Preprocessed { index, offset } =>
            format!("(Circuit.preprocessed c (column := {index}) (row := row) (rotation := {offset}))"),
        CacheVar::Main { index, offset } =>
            format!("(Circuit.main c (column := {index}) (row := row) (rotation := {offset}))"),
        CacheVar::Permutation { index, offset } =>
            format!("(Circuit.permutation c (column := {index}) (row := row) (rotation := {offset}))"),
        CacheVar::Public(index) =>
            format!("(Circuit.public c (index := {index}))"),
        CacheVar::Challenge(index) =>
            format!("(Circuit.challenge c (index := {index}))"),
        CacheVar::IsFirstRow =>
            format!("(Circuit.isFirstRow c row)"),
        CacheVar::IsLastRow =>
            format!("(Circuit.isLastRow c row)"),
        CacheVar::IsTransition =>
            format!("(Circuit.isTransitionRow c row)"),
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum CacheBinaryOp {
    Add,
    Sub,
    Mul
}

fn cache_binary_op_to_lean(x: CacheBinaryOp) -> String {
    match x {
        CacheBinaryOp::Add => format!("+"),
        CacheBinaryOp::Sub => format!("-"),
        CacheBinaryOp::Mul => format!("*"),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CacheSymbolicConstant<F> {
    Leaf(F),
    Neg(Arc<Self>),
    BinaryOp(Arc<Self>, Arc<Self>, CacheBinaryOp),
}

fn cache_symbolic_constant_to_lean<F: Display>(x: &CacheSymbolicConstant<F>) -> String {
    match x {
        CacheSymbolicConstant::Leaf(c) => format!("{c}"),
        CacheSymbolicConstant::Neg(operand) => {
            format!("(-{})", cache_symbolic_constant_to_lean(&operand))
        },
        CacheSymbolicConstant::BinaryOp(lhs, rhs, op) => {
            format!(
                "({} {} {})",
                cache_symbolic_constant_to_lean(&lhs),
                cache_binary_op_to_lean(*op),
                cache_symbolic_constant_to_lean(&rhs)
            )
        },
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CacheOperand<F> {
    Const(CacheSymbolicConstant<F>),
    Var(usize)
}

fn cache_operand_to_lean<F: Display>(x: &CacheOperand<F>) -> String {
    match x {
        CacheOperand::Const(c) => cache_symbolic_constant_to_lean(c),
        CacheOperand::Var(v) => format!("(e{} c row)", *v),
    }
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CacheExpression<F> {
    Const(F),
    Var (CacheVar),
    Negation(CacheOperand<F>),
    BinaryOp{
        lhs: CacheOperand<F>,
        rhs: CacheOperand<F>,
        op: CacheBinaryOp
    },
}

fn cache_expression_to_lean<F: Display>(x: &CacheExpression<F>) -> String {
    match x {
        CacheExpression::Const(c) => format!("{}", c),
        CacheExpression::Var(cache_var) => cache_var_to_lean(*cache_var),
        CacheExpression::Negation(cache_operand) => format!("(-{})", cache_operand_to_lean(cache_operand)),
        CacheExpression::BinaryOp { lhs, rhs, op } =>
            format!(
                "({} {} {})",
                cache_operand_to_lean(lhs),
                cache_binary_op_to_lean(*op),
                cache_operand_to_lean(rhs)
            ),
    }
}

#[derive(Debug)]
pub struct SymbolicCache<F>(pub Vec<CacheExpression<F>>);

pub fn symbolic_cache_to_lean<F: Display>(cache: &SymbolicCache<F>, typename: &str) -> String {
    let args = "{{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ)";

    cache.0.iter()
        .enumerate()
        .map(|(idx, expr)| {
            // println!("{idx}");
            format!("def e{idx} {args} : {typename} :=\n  {}", cache_expression_to_lean(expr))
        })
        .join("\n")
}

#[derive(Clone, Debug)]
pub struct CacheSymbolicVariable<F> {
    pub idx: usize,
    pub cache: Arc<Mutex<SymbolicCache<F>>>,
}

fn cache_symbolic_variable_to_lean<F: Display>(v: &CacheSymbolicVariable<F>) -> String {
    format!("e{} c row", v.idx)
}

#[derive(Copy, Clone, Debug)]
pub enum CopySymbolicVariable {
    Permutation{idx: usize, offset: usize},
    Public{idx: usize},
    Challenge{idx: usize}
}


#[derive(Clone, Debug)]
pub enum CacheSymbolicExpression<F> {
    Variable(CacheSymbolicVariable<F>),
    Constant(CacheSymbolicConstant<F>),
}

pub fn cache_symbolic_expression_to_lean<F: Display>(expr: &CacheSymbolicExpression<F>) -> String {
    match expr {
        CacheSymbolicExpression::Variable(v) => cache_symbolic_variable_to_lean(v),
        CacheSymbolicExpression::Constant(c) => cache_symbolic_constant_to_lean(c),
    }
}

impl <F: Field> From<F> for CacheSymbolicExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant(CacheSymbolicConstant::Leaf(value))
    }
}

impl <F: Field> From<CopySymbolicVariable> for CacheSymbolicExpression<F> {
    fn from(value: CopySymbolicVariable) -> Self {
        let var = CacheExpression::Var(match value {
            CopySymbolicVariable::Permutation { idx, offset } => CacheVar::Permutation { index: idx, offset },
            CopySymbolicVariable::Public { idx } => CacheVar::Public(idx),
            CopySymbolicVariable::Challenge { idx } => CacheVar::Challenge(idx),
        });
        
        let cache = Arc::new(Mutex::new(SymbolicCache(vec![var])));
        CacheSymbolicExpression::Variable(CacheSymbolicVariable {
            idx: 0,
            cache
        })
    }
}

impl <F: Field> From<CacheSymbolicVariable<F>> for CacheSymbolicExpression<F> {
    fn from(value: CacheSymbolicVariable<F>) -> Self {
        Self::Variable(value)
    }
}


impl<F: Field> Default for CacheSymbolicExpression<F> {
    fn default() -> Self {
        Self::from(F::default())
    }
}

impl <F: Field> PrimeCharacteristicRing for CacheSymbolicExpression<F> {
    type PrimeSubfield = F::PrimeSubfield;

    const ZERO: Self = Self::Constant(CacheSymbolicConstant::Leaf(F::ZERO));

    const ONE: Self = Self::Constant(CacheSymbolicConstant::Leaf(F::ONE));

    const TWO: Self = Self::Constant(CacheSymbolicConstant::Leaf(F::TWO));

    const NEG_ONE: Self = Self::Constant(CacheSymbolicConstant::Leaf(F::NEG_ONE));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        F::from_prime_subfield(f).into()
    }
}

impl <F: Field> Neg for CacheSymbolicExpression<F>
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            CacheSymbolicExpression::Variable(v) => {
                let idx = {
                    let mut cache = v.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::Negation(CacheOperand::Var(idx)) => *idx == v.idx,
                        _ => false,
                    }).map(|x| x.0);

                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::Negation(CacheOperand::Var(v.idx)));
                            cache.0.len() - 1
                        }
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: v.cache })
            },
            CacheSymbolicExpression::Constant(c) => {
                Self::Constant(CacheSymbolicConstant::Neg(Arc::new(c)))
            },
        }
    }
}

// Updates the given cache to include everything in the expression's
// Returns the index of the expression in the updated cache
// The expression's cache remains unchanged, so its index in there remains valid
pub fn merge_into_cache<F: Field>(cache: Arc<Mutex<SymbolicCache<F>>>, expr: &CacheSymbolicVariable<F>) -> usize {
    if Arc::ptr_eq(&cache, &expr.cache) {
        expr.idx;
    }

    // Must not lock one cache after another in order to avoid
    // a possible deadlock with two calls running simultaneously with swapped inputs

    // We therefore need to read out the expression's entire cache
    // before we then move it into the given cache

    let local_expr_cache = {
        let cache = &expr.cache.lock().unwrap().0;
        cache.clone()
    };

    // We know that every expression in the cache must only depend on expressions before it
    // Expr cache leaves may already exist in the given cache
    // Expr cache branches may also already exist, but we would need to check for
    // the change of location between where the children existed in the expr cache and where
    // they exist in the given cache
    // Hence we must build up a list of where each expression ends up

    let mut destinations = vec![];

    // Given cache mutex lock zone
    {
        let cache = &mut cache.lock().unwrap();
        for r_expression in local_expr_cache {
            let destination = match r_expression {
                CacheExpression::Const(r) => {
                    match cache.0.iter().find_position(|l_expression| {
                        match l_expression {
                            CacheExpression::Const(l) => *l == r,
                            _ => false
                        }
                    }) {
                        Some((pos, _)) => pos,
                        None => {
                            cache.0.push(r_expression);
                            cache.0.len() - 1
                        },
                    }
                },
                CacheExpression::Var(r_cache_var) => {
                    match cache.0.iter().find_position(|l_expression| {
                        match l_expression {
                            CacheExpression::Var(l_cache_var) => *l_cache_var == r_cache_var,
                            _ => false
                        }
                    }) {
                        Some ((pos, _)) => pos,
                        None => {
                            cache.0.push(r_expression);
                            cache.0.len() - 1
                        }
                    }
                },
                CacheExpression::Negation(cache_operand) => {
                    let translated_op = match cache_operand {
                        CacheOperand::Const(cache_symbolic_constant) => {
                            CacheOperand::Const(cache_symbolic_constant)
                        },
                        CacheOperand::Var(idx) => {
                            CacheOperand::Var(destinations[idx])
                        },
                    };
                    match cache.0.iter().find_position(|l_expression| {
                        match l_expression {
                            CacheExpression::Negation(l) => *l == translated_op,
                            _ => false,
                        }
                    }) {
                        Some((pos, _)) => pos,
                        None => {
                            cache.0.push(CacheExpression::Negation(translated_op));
                            cache.0.len() - 1
                        },
                    }
                },
                CacheExpression::BinaryOp { lhs, rhs, op: r_op } => {
                    let lhs_translated = match lhs {
                        CacheOperand::Const(cache_symbolic_constant) => {
                            CacheOperand::Const(cache_symbolic_constant)
                        },
                        CacheOperand::Var(idx) => {
                            CacheOperand::Var(destinations[idx])
                        },
                    };
                    let rhs_translated = match rhs {
                        CacheOperand::Const(cache_symbolic_constant) => {
                            CacheOperand::Const(cache_symbolic_constant)
                        },
                        CacheOperand::Var(idx) => {
                            CacheOperand::Var(destinations[idx])
                        },
                    };
                    match cache.0.iter().find_position(|l_expression| {
                        match l_expression {
                            CacheExpression::BinaryOp { lhs: l_lhs, rhs: l_rhs, op: l_op } =>
                                *l_lhs == lhs_translated &&
                                *l_rhs == rhs_translated &&
                                *l_op == r_op,
                            _ => false
                        }
                    }) {
                        Some((pos, _)) => pos,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp { lhs: lhs_translated, rhs: rhs_translated, op: r_op });
                            cache.0.len() - 1
                        },
                    }
                },
            };

            destinations.push(destination)
        }

        destinations[expr.idx]
    }
}

impl <F: Field, T> Add<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    type Output = Self;
    
    fn add(self, rhs: T) -> Self::Output {
        match (self, rhs.into()) {
            (Self::Variable(l), Self::Variable(r)) => {
                merge_into_cache(l.cache.clone(), &r);

                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Add
                        } => *lhs == l.idx && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Add
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Variable(l), Self::Constant(r)) => {
                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Const(rhs),
                            op: CacheBinaryOp::Add
                        } => *lhs == l.idx && *rhs == r,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Const(r),
                                op: CacheBinaryOp::Add
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Constant(l), Self::Variable(r)) => {
                let idx = {
                    let mut cache = r.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Const(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Add
                        } => *lhs == l && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Const(l),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Add
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: r.cache })
            },
            (Self::Constant(l), Self::Constant(r)) => {
                Self::Constant(
                    CacheSymbolicConstant::BinaryOp(
                        Arc::new(l),
                        Arc::new(r),
                        CacheBinaryOp::Add
                    )
                )
            },
        }
    }
}

impl <F: Field, T> AddAssign<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    fn add_assign(&mut self, rhs: T) {
        *self = self.clone() + rhs.into();
    }
}

impl<F: Field, T> Sum<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into)
            .reduce(|x, y| x + y)
            .unwrap_or(Self::ZERO)
    }
}

impl <F: Field, T> Sub<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    type Output = Self;
    
    fn sub(self, rhs: T) -> Self::Output {
        match (self, rhs.into()) {
            (Self::Variable(l), Self::Variable(r)) => {
                merge_into_cache(l.cache.clone(), &r);

                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Sub
                        } => *lhs == l.idx && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Sub
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Variable(l), Self::Constant(r)) => {
                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Const(rhs),
                            op: CacheBinaryOp::Sub
                        } => *lhs == l.idx && *rhs == r,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Const(r),
                                op: CacheBinaryOp::Sub
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Constant(l), Self::Variable(r)) => {
                let idx = {
                    let mut cache = r.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Const(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Sub
                        } => *lhs == l && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Const(l),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Sub
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: r.cache })
            },
            (Self::Constant(l), Self::Constant(r)) => {
                Self::Constant(
                    CacheSymbolicConstant::BinaryOp(
                        Arc::new(l),
                        Arc::new(r),
                        CacheBinaryOp::Sub
                    )
                )
            },
        }
    }
}

impl <F: Field, T> SubAssign<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    fn sub_assign(&mut self, rhs: T) {
        *self = self.clone() + rhs.into();
    }
}

impl <F: Field, T> Mul<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    type Output = Self;
    
    fn mul(self, rhs: T) -> Self::Output {
        match (self, rhs.into()) {
            (Self::Variable(l), Self::Variable(r)) => {
                merge_into_cache(l.cache.clone(), &r);

                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Mul
                        } => *lhs == l.idx && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Mul
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Variable(l), Self::Constant(r)) => {
                let idx = {
                    let mut cache = l.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Var(lhs),
                            rhs: CacheOperand::Const(rhs),
                            op: CacheBinaryOp::Mul
                        } => *lhs == l.idx && *rhs == r,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Var(l.idx),
                                rhs: CacheOperand::Const(r),
                                op: CacheBinaryOp::Mul
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: l.cache })
            },
            (Self::Constant(l), Self::Variable(r)) => {
                let idx = {
                    let mut cache = r.cache.lock().unwrap();
                    let position = cache.0.iter().find_position(|x| match x {
                        CacheExpression::BinaryOp {
                            lhs: CacheOperand::Const(lhs),
                            rhs: CacheOperand::Var(rhs),
                            op: CacheBinaryOp::Mul
                        } => *lhs == l && *rhs == r.idx,
                        _ => false,
                    }).map(|x| x.0);
    
                    match position {
                        Some(idx) => idx,
                        None => {
                            cache.0.push(CacheExpression::BinaryOp {
                                lhs: CacheOperand::Const(l),
                                rhs: CacheOperand::Var(r.idx),
                                op: CacheBinaryOp::Mul
                            });
                            cache.0.len() - 1
                        },
                    }
                };

                Self::Variable(CacheSymbolicVariable { idx, cache: r.cache })
            },
            (Self::Constant(l), Self::Constant(r)) => {
                Self::Constant(
                    CacheSymbolicConstant::BinaryOp(
                        Arc::new(l),
                        Arc::new(r),
                        CacheBinaryOp::Mul
                    )
                )
            },
        }
    }
}

impl <F: Field, T> MulAssign<T> for CacheSymbolicExpression<F>
where
    T: Into<Self>
{
    fn mul_assign(&mut self, rhs: T) {
        *self = self.clone() + rhs.into();
    }
}

impl<F: Field, T: Into<Self>> Product<T> for CacheSymbolicExpression<F> {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into)
            .reduce(|x, y| x * y)
            .unwrap_or(Self::ONE)
    }
}

impl<F: Field> Algebra<F> for CacheSymbolicExpression<F> {}
impl<F: Field> Algebra<CacheSymbolicVariable<F>> for CacheSymbolicExpression<F> {}
impl<F: Field + InjectiveMonomial<N>, const N: u64> InjectiveMonomial<N> for CacheSymbolicExpression<F> {}

impl <F: Field> Add<F> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn add(self, rhs: F) -> Self::Output {
        CacheSymbolicExpression::from(self) +
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Add<CacheSymbolicVariable<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn add(self, rhs: CacheSymbolicVariable<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) +
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Add<CacheSymbolicExpression<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn add(self, rhs: CacheSymbolicExpression<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) + rhs
    }
}

impl <F: Field> Sub<F> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        CacheSymbolicExpression::from(self) -
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Sub<CacheSymbolicVariable<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn sub(self, rhs: CacheSymbolicVariable<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) -
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Sub<CacheSymbolicExpression<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn sub(self, rhs: CacheSymbolicExpression<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) - rhs
    }
}

impl <F: Field> Mul<F> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        CacheSymbolicExpression::from(self) *
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Mul<CacheSymbolicVariable<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn mul(self, rhs: CacheSymbolicVariable<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) *
        CacheSymbolicExpression::from(rhs)
    }
}

impl <F: Field> Mul<CacheSymbolicExpression<F>> for CacheSymbolicVariable<F> {
    type Output = CacheSymbolicExpression<F>;

    fn mul(self, rhs: CacheSymbolicExpression<F>) -> Self::Output {
        CacheSymbolicExpression::from(self) * rhs
    }
}

// #[derive(Debug)]
// pub struct SymbolicExpressionCache<F>(Vec<usize>);


// /// A variable within the evaluation window, i.e. a column in either the local or next row.
// #[derive(Clone, Debug)]
// pub struct SymbolicVariable<F> {
//     pub entry: Entry,
//     pub index: usize,
//     pub cache: Arc<SymbolicExpressionCache<F>>,
//     pub(crate) _phantom: PhantomData<F>,
// }

// impl<F> SymbolicVariable<F> {
//     pub const fn new(entry: Entry, index: usize, cache: Arc<SymbolicExpressionCache<F>>) -> Self {
//         cache.0.push(0);
//         Self {
//             entry,
//             index,
//             cache,
//             _phantom: PhantomData,
//         }
//     }

//     pub const fn degree_multiple(&self) -> usize {
//         match self.entry {
//             Entry::Preprocessed { .. } | Entry::Main { .. } | Entry::Permutation { .. } => 1,
//             Entry::Public | Entry::Challenge => 0,
//         }
//     }
// }

// impl<F: Field, T> Add<T> for SymbolicVariable<F>
// where
// T: Into<SymbolicExpression<F>>,
// {
//     type Output = SymbolicExpression<F>;
    
//     fn add(self, rhs: T) -> Self::Output {
//         SymbolicExpression::from(self) + rhs.into()
//     }
// }

// impl<F: Field, T> Sub<T> for SymbolicVariable<F>
// where
// T: Into<SymbolicExpression<F>>,
// {
//     type Output = SymbolicExpression<F>;
    
//     fn sub(self, rhs: T) -> Self::Output {
//         SymbolicExpression::from(self) - rhs.into()
//     }
// }

// impl<F: Field, T> Mul<T> for SymbolicVariable<F>
// where
// T: Into<SymbolicExpression<F>>,
// {
//     type Output = SymbolicExpression<F>;
    
//     fn mul(self, rhs: T) -> Self::Output {
//         SymbolicExpression::from(self) * rhs.into()
//     }
// }


// /// An expression over `SymbolicVariable`s.
// #[derive(Clone, Debug)]
// pub enum SymbolicExpression<F> {
//     Variable(SymbolicVariable<F>),
//     IsFirstRow,
//     IsLastRow,
//     IsTransition,
//     Constant(F),
//     Add {
//         x: Rc<Self>,
//         y: Rc<Self>,
//         degree_multiple: usize,
//     },
//     Sub {
//         x: Rc<Self>,
//         y: Rc<Self>,
//         degree_multiple: usize,
//     },
//     Neg {
//         x: Rc<Self>,
//         degree_multiple: usize,
//     },
//     Mul {
//         x: Rc<Self>,
//         y: Rc<Self>,
//         degree_multiple: usize,
//     },
// }

// impl<F: Field> From<SymbolicVariable<F>> for SymbolicExpression<F> {
//     fn from(value: SymbolicVariable<F>) -> Self {
//         Self::Variable(value)
//     }
// }

// impl<F> SymbolicExpression<F> {
//     /// Returns the multiple of `n` (the trace length) in this expression's degree.
//     pub const fn degree_multiple(&self) -> usize {
//         match self {
//             Self::Variable(v) => v.degree_multiple(),
//             Self::IsFirstRow | Self::IsLastRow => 1,
//             Self::IsTransition | Self::Constant(_) => 0,
//             Self::Add {
//                 degree_multiple, ..
//             }
//             | Self::Sub {
//                 degree_multiple, ..
//             }
//             | Self::Neg {
//                 degree_multiple, ..
//             }
//             | Self::Mul {
//                 degree_multiple, ..
//             } => *degree_multiple,
//         }
//     }
// }

// impl<F: Field> Default for SymbolicExpression<F> {
//     fn default() -> Self {
//         Self::Constant(F::ZERO)
//     }
// }

// impl<F: Field> From<F> for SymbolicExpression<F> {
//     fn from(value: F) -> Self {
//         Self::Constant(value)
//     }
// }

// impl<F: Field> PrimeCharacteristicRing for SymbolicExpression<F> {
//     type PrimeSubfield = F::PrimeSubfield;

//     const ZERO: Self = Self::Constant(F::ZERO);
//     const ONE: Self = Self::Constant(F::ONE);
//     const TWO: Self = Self::Constant(F::TWO);
//     const NEG_ONE: Self = Self::Constant(F::NEG_ONE);

//     #[inline]
//     fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
//         F::from_prime_subfield(f).into()
//     }
// }

// impl<F: Field> Algebra<F> for SymbolicExpression<F> {}

// impl<F: Field> Algebra<SymbolicVariable<F>> for SymbolicExpression<F> {}

// // Note we cannot implement PermutationMonomial due to the degree_multiple part which makes
// // operations non invertible.
// impl<F: Field + InjectiveMonomial<N>, const N: u64> InjectiveMonomial<N> for SymbolicExpression<F> {}

// impl<F: Field, T> Add<T> for SymbolicExpression<F>
// where
//     T: Into<Self>,
// {
//     type Output = Self;

//     fn add(self, rhs: T) -> Self {
//         match (self, rhs.into()) {
//             (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs + rhs),
//             (lhs, rhs) => Self::Add {
//                 degree_multiple: lhs.degree_multiple().max(rhs.degree_multiple()),
//                 x: Rc::new(lhs),
//                 y: Rc::new(rhs),
//             },
//         }
//     }
// }

// impl<F: Field, T> AddAssign<T> for SymbolicExpression<F>
// where
//     T: Into<Self>,
// {
//     fn add_assign(&mut self, rhs: T) {
//         *self = self.clone() + rhs.into();
//     }
// }

// impl<F: Field, T> Sum<T> for SymbolicExpression<F>
// where
//     T: Into<Self>,
// {
//     fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
//         iter.map(Into::into)
//             .reduce(|x, y| x + y)
//             .unwrap_or(Self::ZERO)
//     }
// }

// impl<F: Field, T: Into<Self>> Sub<T> for SymbolicExpression<F> {
//     type Output = Self;

//     fn sub(self, rhs: T) -> Self {
//         match (self, rhs.into()) {
//             (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs - rhs),
//             (lhs, rhs) => Self::Sub {
//                 degree_multiple: lhs.degree_multiple().max(rhs.degree_multiple()),
//                 x: Rc::new(lhs),
//                 y: Rc::new(rhs),
//             },
//         }
//     }
// }

// impl<F: Field, T> SubAssign<T> for SymbolicExpression<F>
// where
//     T: Into<Self>,
// {
//     fn sub_assign(&mut self, rhs: T) {
//         *self = self.clone() - rhs.into();
//     }
// }

// impl<F: Field> Neg for SymbolicExpression<F> {
//     type Output = Self;

//     fn neg(self) -> Self {
//         match self {
//             Self::Constant(c) => Self::Constant(-c),
//             expr => Self::Neg {
//                 degree_multiple: expr.degree_multiple(),
//                 x: Rc::new(expr),
//             },
//         }
//     }
// }

// impl<F: Field, T: Into<Self>> Mul<T> for SymbolicExpression<F> {
//     type Output = Self;

//     fn mul(self, rhs: T) -> Self {
//         match (self, rhs.into()) {
//             (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs * rhs),
//             (lhs, rhs) => Self::Mul {
//                 degree_multiple: lhs.degree_multiple() + rhs.degree_multiple(),
//                 x: Rc::new(lhs),
//                 y: Rc::new(rhs),
//             },
//         }
//     }
// }

// impl<F: Field, T> MulAssign<T> for SymbolicExpression<F>
// where
//     T: Into<Self>,
// {
//     fn mul_assign(&mut self, rhs: T) {
//         *self = self.clone() * rhs.into();
//     }
// }

// impl<F: Field, T: Into<Self>> Product<T> for SymbolicExpression<F> {
//     fn product<I: Iterator<Item = T>>(iter: I) -> Self {
//         iter.map(Into::into)
//             .reduce(|x, y| x * y)
//             .unwrap_or(Self::ONE)
//     }
// }

// #[cfg(test)]
// mod tests {
//     use alloc::vec;

//     use p3_baby_bear::BabyBear;

//     use super::*;
//     use crate::symbolic_variable::Entry;

//     #[test]
//     fn test_symbolic_expression_degree_multiple() {
//         let constant_expr = SymbolicExpression::<BabyBear>::Constant(BabyBear::new(5));
//         assert_eq!(
//             constant_expr.degree_multiple(),
//             0,
//             "Constant should have degree 0"
//         );

//         let variable_expr =
//             SymbolicExpression::Variable(SymbolicVariable::new(Entry::Main { offset: 0 }, 1));
//         assert_eq!(
//             variable_expr.degree_multiple(),
//             1,
//             "Main variable should have degree 1"
//         );

//         let preprocessed_var = SymbolicExpression::Variable(SymbolicVariable::new(
//             Entry::Preprocessed { offset: 0 },
//             2,
//         ));
//         assert_eq!(
//             preprocessed_var.degree_multiple(),
//             1,
//             "Preprocessed variable should have degree 1"
//         );

//         let permutation_var = SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(
//             Entry::Permutation { offset: 0 },
//             3,
//         ));
//         assert_eq!(
//             permutation_var.degree_multiple(),
//             1,
//             "Permutation variable should have degree 1"
//         );

//         let public_var =
//             SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(Entry::Public, 4));
//         assert_eq!(
//             public_var.degree_multiple(),
//             0,
//             "Public variable should have degree 0"
//         );

//         let challenge_var =
//             SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(Entry::Challenge, 5));
//         assert_eq!(
//             challenge_var.degree_multiple(),
//             0,
//             "Challenge variable should have degree 0"
//         );

//         let is_first_row = SymbolicExpression::<BabyBear>::IsFirstRow;
//         assert_eq!(
//             is_first_row.degree_multiple(),
//             1,
//             "IsFirstRow should have degree 1"
//         );

//         let is_last_row = SymbolicExpression::<BabyBear>::IsLastRow;
//         assert_eq!(
//             is_last_row.degree_multiple(),
//             1,
//             "IsLastRow should have degree 1"
//         );

//         let is_transition = SymbolicExpression::<BabyBear>::IsTransition;
//         assert_eq!(
//             is_transition.degree_multiple(),
//             0,
//             "IsTransition should have degree 0"
//         );

//         let add_expr = SymbolicExpression::<BabyBear>::Add {
//             x: Rc::new(variable_expr.clone()),
//             y: Rc::new(preprocessed_var.clone()),
//             degree_multiple: 1,
//         };
//         assert_eq!(
//             add_expr.degree_multiple(),
//             1,
//             "Addition should take max degree of inputs"
//         );

//         let sub_expr = SymbolicExpression::<BabyBear>::Sub {
//             x: Rc::new(variable_expr.clone()),
//             y: Rc::new(preprocessed_var.clone()),
//             degree_multiple: 1,
//         };
//         assert_eq!(
//             sub_expr.degree_multiple(),
//             1,
//             "Subtraction should take max degree of inputs"
//         );

//         let neg_expr = SymbolicExpression::<BabyBear>::Neg {
//             x: Rc::new(variable_expr.clone()),
//             degree_multiple: 1,
//         };
//         assert_eq!(
//             neg_expr.degree_multiple(),
//             1,
//             "Negation should keep the degree"
//         );

//         let mul_expr = SymbolicExpression::<BabyBear>::Mul {
//             x: Rc::new(variable_expr.clone()),
//             y: Rc::new(preprocessed_var.clone()),
//             degree_multiple: 2,
//         };
//         assert_eq!(
//             mul_expr.degree_multiple(),
//             2,
//             "Multiplication should sum degrees"
//         );
//     }

//     #[test]
//     fn test_addition_of_constants() {
//         let a = SymbolicExpression::Constant(BabyBear::new(3));
//         let b = SymbolicExpression::Constant(BabyBear::new(4));
//         let result = a + b;
//         match result {
//             SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(7)),
//             _ => panic!("Addition of constants did not simplify correctly"),
//         }
//     }

//     #[test]
//     fn test_subtraction_of_constants() {
//         let a = SymbolicExpression::Constant(BabyBear::new(10));
//         let b = SymbolicExpression::Constant(BabyBear::new(4));
//         let result = a - b;
//         match result {
//             SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(6)),
//             _ => panic!("Subtraction of constants did not simplify correctly"),
//         }
//     }

//     #[test]
//     fn test_negation() {
//         let a = SymbolicExpression::Constant(BabyBear::new(7));
//         let result = -a;
//         match result {
//             SymbolicExpression::Constant(val) => {
//                 assert_eq!(val, BabyBear::NEG_ONE * BabyBear::new(7))
//             }
//             _ => panic!("Negation did not work correctly"),
//         }
//     }

//     #[test]
//     fn test_multiplication_of_constants() {
//         let a = SymbolicExpression::Constant(BabyBear::new(3));
//         let b = SymbolicExpression::Constant(BabyBear::new(5));
//         let result = a * b;
//         match result {
//             SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(15)),
//             _ => panic!("Multiplication of constants did not simplify correctly"),
//         }
//     }

//     #[test]
//     fn test_degree_multiple_for_addition() {
//         let a = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
//             Entry::Main { offset: 0 },
//             1,
//         ));
//         let b = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
//             Entry::Main { offset: 0 },
//             2,
//         ));
//         let result = a.clone() + b.clone();
//         match result {
//             SymbolicExpression::Add {
//                 degree_multiple,
//                 x,
//                 y,
//             } => {
//                 assert_eq!(degree_multiple, 1);
//                 assert!(
//                     matches!(*x, SymbolicExpression::Variable(ref v) if v.index == 1 && matches!(v.entry, Entry::Main { offset: 0 }))
//                 );
//                 assert!(
//                     matches!(*y, SymbolicExpression::Variable(ref v) if v.index == 2 && matches!(v.entry, Entry::Main { offset: 0 }))
//                 );
//             }
//             _ => panic!("Addition did not create an Add expression"),
//         }
//     }

//     #[test]
//     fn test_degree_multiple_for_multiplication() {
//         let a = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
//             Entry::Main { offset: 0 },
//             1,
//         ));
//         let b = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
//             Entry::Main { offset: 0 },
//             2,
//         ));
//         let result = a.clone() * b.clone();

//         match result {
//             SymbolicExpression::Mul {
//                 degree_multiple,
//                 x,
//                 y,
//             } => {
//                 assert_eq!(degree_multiple, 2, "Multiplication should sum degrees");

//                 assert!(
//                     matches!(*x, SymbolicExpression::Variable(ref v)
//                         if v.index == 1 && matches!(v.entry, Entry::Main { offset: 0 })
//                     ),
//                     "Left operand should match `a`"
//                 );

//                 assert!(
//                     matches!(*y, SymbolicExpression::Variable(ref v)
//                         if v.index == 2 && matches!(v.entry, Entry::Main { offset: 0 })
//                     ),
//                     "Right operand should match `b`"
//                 );
//             }
//             _ => panic!("Multiplication did not create a `Mul` expression"),
//         }
//     }

//     #[test]
//     fn test_sum_operator() {
//         let expressions = vec![
//             SymbolicExpression::Constant(BabyBear::new(2)),
//             SymbolicExpression::Constant(BabyBear::new(3)),
//             SymbolicExpression::Constant(BabyBear::new(5)),
//         ];
//         let result: SymbolicExpression<BabyBear> = expressions.into_iter().sum();
//         match result {
//             SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(10)),
//             _ => panic!("Sum did not produce correct result"),
//         }
//     }

//     #[test]
//     fn test_product_operator() {
//         let expressions = vec![
//             SymbolicExpression::Constant(BabyBear::new(2)),
//             SymbolicExpression::Constant(BabyBear::new(3)),
//             SymbolicExpression::Constant(BabyBear::new(4)),
//         ];
//         let result: SymbolicExpression<BabyBear> = expressions.into_iter().product();
//         match result {
//             SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(24)),
//             _ => panic!("Product did not produce correct result"),
//         }
//     }
// }
