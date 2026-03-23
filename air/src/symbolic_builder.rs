use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};

use alloc::vec;
use alloc::vec::Vec;

use itertools::Itertools;
use p3_field::{Algebra, ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;

use crate::symbolic_expression::SymbolicExpression;
use crate::symbolic_variable::{Entry, SymbolicVariable};
use crate::{
    AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, InteractionAirBuilder, PairBuilder,
    PermutationAirBuilder,
};

fn indent(code: String, indentation: &str) -> String {
    code.split("\n").map(|line| format!("{indentation}{line}")).join("\n")
}

fn symbolic_expression_size<F>(x: &SymbolicExpression<F>) -> usize {
    match x {
        SymbolicExpression::Variable(_) => 1,
        SymbolicExpression::IsFirstRow => 1,
        SymbolicExpression::IsLastRow => 1,
        SymbolicExpression::IsTransition => 1,
        SymbolicExpression::Constant(_) => 1,
        SymbolicExpression::Add { x, y, degree_multiple: _ } => {
            1 + symbolic_expression_size(&x) + symbolic_expression_size(&y)
        },
        SymbolicExpression::Sub { x, y, degree_multiple: _ } => {
            1 + symbolic_expression_size(&x) + symbolic_expression_size(&y)
        },
        SymbolicExpression::Neg { x, degree_multiple: _ } => {
            1 + symbolic_expression_size(&x)
        },
        SymbolicExpression::Mul { x, y, degree_multiple: _ } => {
            1 + symbolic_expression_size(&x) + symbolic_expression_size(&y)
        },
    }
}

fn sort_by_argument_order<F: Field>(lhs: &SymbolicExpression<F>, rhs: &SymbolicExpression<F>) -> Ordering {
    match (lhs, rhs) {
        (SymbolicExpression::Variable(lhs), SymbolicExpression::Variable(rhs)) => match (lhs.entry, rhs.entry) {
            (Entry::Preprocessed { offset: l }, Entry::Preprocessed { offset: r }) => lhs.index.cmp(&rhs.index).then(l.cmp(&r)),
            (Entry::Preprocessed { offset: _ }, Entry::Main { offset: _ }) => Ordering::Greater,
            (Entry::Preprocessed { offset: _ }, Entry::Permutation { offset: _ }) => Ordering::Greater,
            (Entry::Preprocessed { offset: _ }, Entry::Public) => Ordering::Greater,
            (Entry::Preprocessed { offset: _ }, Entry::Challenge) => Ordering::Greater,
            (Entry::Main { offset: _ }, Entry::Preprocessed { offset: _ }) => Ordering::Less,
            (Entry::Main { offset: l }, Entry::Main { offset: r }) => lhs.index.cmp(&rhs.index).then(l.cmp(&r)),
            (Entry::Main { offset: _ }, Entry::Permutation { offset: _ }) => Ordering::Greater,
            (Entry::Main { offset: _ }, Entry::Public) => Ordering::Greater,
            (Entry::Main { offset: _ }, Entry::Challenge) => Ordering::Greater,
            (Entry::Permutation { offset: _ }, Entry::Preprocessed { offset: _ }) => Ordering::Less,
            (Entry::Permutation { offset: _ }, Entry::Main { offset: _ }) => Ordering::Less,
            (Entry::Permutation { offset: l }, Entry::Permutation { offset: r }) => lhs.index.cmp(&rhs.index).then(l.cmp(&r)),
            (Entry::Permutation { offset: _ }, Entry::Public) => Ordering::Greater,
            (Entry::Permutation { offset: _ }, Entry::Challenge) => Ordering::Greater,
            (Entry::Public, Entry::Preprocessed { offset: _ }) => Ordering::Less,
            (Entry::Public, Entry::Main { offset: _ }) => Ordering::Less,
            (Entry::Public, Entry::Permutation { offset: _ }) => Ordering::Less,
            (Entry::Public, Entry::Public) => lhs.index.cmp(&rhs.index),
            (Entry::Public, Entry::Challenge) => Ordering::Greater,
            (Entry::Challenge, Entry::Preprocessed { offset: _ }) => Ordering::Less,
            (Entry::Challenge, Entry::Main { offset: _ }) => Ordering::Less,
            (Entry::Challenge, Entry::Permutation { offset: _ }) => Ordering::Less,
            (Entry::Challenge, Entry::Public) => Ordering::Less,
            (Entry::Challenge, Entry::Challenge) => lhs.index.cmp(&rhs.index),
        },
        (SymbolicExpression::Variable(_), _) => Ordering::Less,
        (SymbolicExpression::IsFirstRow, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::IsFirstRow, SymbolicExpression::IsFirstRow) => Ordering::Equal,
        (SymbolicExpression::IsFirstRow, _) => Ordering::Less,
        (SymbolicExpression::IsLastRow, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::IsLastRow, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::IsLastRow, SymbolicExpression::IsLastRow) => Ordering::Equal,
        (SymbolicExpression::IsLastRow, _) => Ordering::Less,
        (SymbolicExpression::IsTransition, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::IsTransition, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::IsTransition, SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::IsTransition, SymbolicExpression::IsTransition) => Ordering::Equal,
        (SymbolicExpression::IsTransition, _) => Ordering::Less,
        (SymbolicExpression::Constant(_), SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::Constant(_), SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::Constant(_), SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::Constant(_), SymbolicExpression::IsTransition) => Ordering::Greater,
        (SymbolicExpression::Constant(l), SymbolicExpression::Constant(r)) => {
            println!("{l}");
            println!("{r}");
            l.to_string().cmp(&r.to_string())
        },
        (SymbolicExpression::Constant(_), _) => Ordering::Less,

        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsTransition) => Ordering::Greater,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Constant(_)) => Ordering::Greater,
        (SymbolicExpression::Add { x: lx, y: ly, degree_multiple: ld }, SymbolicExpression::Add { x: rx, y: ry, degree_multiple: rd }) => {
            sort_by_argument_order(&lx, &rx)
                .then(sort_by_argument_order(&ly, &ry))
                .then(ld.cmp(&rd))
        },
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }) => Ordering::Less,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Neg { x: _, degree_multiple: _ }) => Ordering::Less,
        (SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }) => Ordering::Less,

        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsTransition) => Ordering::Greater,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Constant(_)) => Ordering::Greater,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Sub { x: lx, y: ly, degree_multiple: ld }, SymbolicExpression::Sub { x: rx, y: ry, degree_multiple: rd }) => {
            sort_by_argument_order(&lx, &rx)
                .then(sort_by_argument_order(&ly, &ry))
                .then(ld.cmp(&rd))
        },
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Neg { x: _, degree_multiple: _ }) => Ordering::Less,
        (SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }) => Ordering::Less,

        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::IsTransition) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::Constant(_)) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Neg { x: lx, degree_multiple: ld }, SymbolicExpression::Neg { x: rx, degree_multiple: rd }) => {
            sort_by_argument_order(&lx, &rx)
                .then(ld.cmp(&rd))
        },
        (SymbolicExpression::Neg { x: _, degree_multiple: _ }, SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }) => Ordering::Less,

        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Variable(_)) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsFirstRow) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsLastRow) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::IsTransition) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Constant(_)) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Add { x: _, y: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Sub { x: _, y: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Mul { x: _, y: _, degree_multiple: _ }, SymbolicExpression::Neg { x: _, degree_multiple: _ }) => Ordering::Greater,
        (SymbolicExpression::Mul { x: lx, y: ly, degree_multiple: ld }, SymbolicExpression::Mul { x: rx, y: ry, degree_multiple: rd }) => {
            sort_by_argument_order(&lx, &rx)
                .then(sort_by_argument_order(&ly, &ry))
                .then(ld.cmp(&rd))
        },
    }
}

pub fn symbolic_expression_to_lean_string<F: Field>(
    x: &SymbolicExpression<F>,
    characteristic: Option<u32>,
) -> String {
    match x {
        SymbolicExpression::Variable(symbolic_variable) =>
            match symbolic_variable.entry {
                Entry::Preprocessed { offset } => format!(
                    "(Circuit.preprocessed c (column := {}) (row := row) (rotation := {offset}))",
                    symbolic_variable.index
                ),
                Entry::Main { offset } => format!(
                    "(Circuit.main c (column := {}) (row := row) (rotation := {offset}))",
                    symbolic_variable.index
                ),
                Entry::Permutation { offset } => format!(
                    "(Circuit.permutation c (column := {}) (row := row) (rotation := {offset}))",
                    symbolic_variable.index
                ),
                Entry::Public =>
                    format!("(Circuit.public c (index := {}))", symbolic_variable.index),
                Entry::Challenge => format!(
                    "(Circuit.challenge c (index := {}))",
                    symbolic_variable.index
                ),
            },
        SymbolicExpression::IsFirstRow => format!("(Circuit.isFirstRow c row)"),
        SymbolicExpression::IsLastRow => format!("(Circuit.isLastRow c row)"),
        SymbolicExpression::IsTransition => format!("(Circuit.isTransitionRow c row)"),
        SymbolicExpression::Constant(x) => {
            let num = str::parse::<u32>(&format!("{x}"));
            match num {
                Ok(num) => match characteristic {
                    Some(characteristic) => {
                        if num >= characteristic {
                            format!("{x}")
                        } else if characteristic - num < num {
                            format!("-{}", characteristic - num)
                        } else {
                            format!("{x}")
                        }
                    }
                    None => format!("{x}"),
                },
                Err(_) => format!("{x}"),
            }
        }
        SymbolicExpression::Add {
            x,
            y,
            degree_multiple: _degree_multiple,
        } => {
            let lhs = symbolic_expression_to_lean_string(&x, characteristic);
            let rhs = symbolic_expression_to_lean_string(&y, characteristic);
            format!("({lhs} + {rhs})")
        }
        SymbolicExpression::Sub {
            x,
            y,
            degree_multiple: _degree_multiple,
        } => {
            let lhs = symbolic_expression_to_lean_string(&x, characteristic);
            let rhs = symbolic_expression_to_lean_string(&y, characteristic);
            format!("({lhs} - {rhs})")
        }
        SymbolicExpression::Neg {
            x,
            degree_multiple: _degree_multiple,
        } => {
            let leaf = symbolic_expression_to_lean_string(&x, characteristic);
            format!("-({leaf})")
        }
        SymbolicExpression::Mul {
            x,
            y,
            degree_multiple: _degree_multiple,
        } => {
            let lhs = symbolic_expression_to_lean_string(&x, characteristic);
            let rhs = symbolic_expression_to_lean_string(&y, characteristic);
            format!("({lhs} * {rhs})")
        }
    }
}

struct OrderedSymbolicExpression<F: Field>(SymbolicExpression<F>);

impl<F: Field> PartialEq for OrderedSymbolicExpression<F> {
    fn eq(&self, other: &Self) -> bool {
        sort_by_argument_order(&self.0, &other.0) == Ordering::Equal
    }
}

impl<F: Field> Eq for OrderedSymbolicExpression<F> {   
}

impl<F: Field> PartialOrd for OrderedSymbolicExpression<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(sort_by_argument_order(&self.0, &other.0))
    }
}

impl<F: Field> Ord for OrderedSymbolicExpression<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        sort_by_argument_order(&self.0, &other.0)
    }
}

fn get_symbolic_variable_leaf_string_set<F: Field>(
    x: &SymbolicExpression<F>,
) -> BTreeSet<OrderedSymbolicExpression<F>> {
    match x {
        SymbolicExpression::Variable(_symbolic_variable) => {
            let mut set = BTreeSet::new();
            set.insert(OrderedSymbolicExpression(x.clone()));
            set
        },
        SymbolicExpression::IsFirstRow => {
            let mut set = BTreeSet::new();
            set.insert(OrderedSymbolicExpression(x.clone()));
            set
        },
        SymbolicExpression::IsLastRow => {
            let mut set = BTreeSet::new();
            set.insert(OrderedSymbolicExpression(x.clone()));
            set
        },
        SymbolicExpression::IsTransition => {
            let mut set = BTreeSet::new();
            set.insert(OrderedSymbolicExpression(x.clone()));
            set
        },
        SymbolicExpression::Constant(_) => {
            let mut set = BTreeSet::new();
            set.insert(OrderedSymbolicExpression(x.clone()));
            set
        },
        SymbolicExpression::Add { x, y, degree_multiple: _ } => {
            let mut set = get_symbolic_variable_leaf_string_set(&x);
            set.append(&mut get_symbolic_variable_leaf_string_set(&y));
            set
        },
        SymbolicExpression::Sub { x, y, degree_multiple: _ } => {
            let mut set = get_symbolic_variable_leaf_string_set(&x);
            set.append(&mut get_symbolic_variable_leaf_string_set(&y));
            set
        },
        SymbolicExpression::Neg { x, degree_multiple: _ } => {
            get_symbolic_variable_leaf_string_set(&x)
        }
        SymbolicExpression::Mul { x, y, degree_multiple: _ } => {
            let mut set = get_symbolic_variable_leaf_string_set(&x);
            set.append(&mut get_symbolic_variable_leaf_string_set(&y));
            set
        },
    }
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
enum CachedBinaryOp {
    Add,
    Sub,
    Mul
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
enum CachedSymbolicExpression {
    Leaf(String),
    Neg(usize),
    Binary{
        lhs: usize,
        rhs: usize,
        op: CachedBinaryOp
    },
}

fn cache_symbolic_expression_walk_leaf<F: Field>(
    x: &SymbolicExpression<F>,
    characteristic: Option<u32>,
    cache: &mut HashMap<CachedSymbolicExpression, usize>
) -> usize {    
    let str = symbolic_expression_to_lean_string(&x, characteristic);
    let node = CachedSymbolicExpression::Leaf(str);

    match cache.get(&node) {
        Some(x) => *x,
        None => {
            let idx = cache.len();
            cache.insert(node, idx);
            idx
        },
    }
}

fn cache_symbolic_expression_walk_binary<F: Field>(
    lhs: &SymbolicExpression<F>,
    rhs: &SymbolicExpression<F>,
    node_op: CachedBinaryOp,
    characteristic: Option<u32>,
    cache: &mut HashMap<CachedSymbolicExpression, usize>
) -> usize {
    let left_child = cache_symbolic_expression_walk(lhs, characteristic, cache);
    let right_child = cache_symbolic_expression_walk(rhs, characteristic, cache);
    let node = CachedSymbolicExpression::Binary {
        lhs: left_child,
        rhs: right_child,
        op: node_op
    };

    match cache.get(&node) {
        Some(x) => *x,
        None => {
            let idx = cache.len();
            cache.insert(node, idx);
            idx
        },
    }
}

fn cache_symbolic_expression_walk<F: Field>(
    x: &SymbolicExpression<F>,
    characteristic: Option<u32>,
    cache: &mut HashMap<CachedSymbolicExpression, usize>
) -> usize {
    // println!("Cache size: {}", cache.len());
    match x {
        SymbolicExpression::Variable(_) => cache_symbolic_expression_walk_leaf(x, characteristic, cache),
        SymbolicExpression::IsFirstRow => cache_symbolic_expression_walk_leaf(x, characteristic, cache),
        SymbolicExpression::IsLastRow => cache_symbolic_expression_walk_leaf(x, characteristic, cache),
        SymbolicExpression::IsTransition => cache_symbolic_expression_walk_leaf(x, characteristic, cache),
        SymbolicExpression::Constant(_) => cache_symbolic_expression_walk_leaf(x, characteristic, cache),
        SymbolicExpression::Neg { x, degree_multiple: _ } => {
            let child = cache_symbolic_expression_walk(x, characteristic, cache);
            let node = CachedSymbolicExpression::Neg(child);

            match cache.get(&node) {
                Some(x) => *x,
                None => {
                    let idx = cache.len();
                    cache.insert(node, idx);
                    idx
                },
            }
        },
        SymbolicExpression::Add { x, y, degree_multiple: _ } =>
            cache_symbolic_expression_walk_binary(&x, &y, CachedBinaryOp::Add, characteristic, cache),
        SymbolicExpression::Sub { x, y, degree_multiple: _ } =>
            cache_symbolic_expression_walk_binary(&x, &y, CachedBinaryOp::Sub, characteristic, cache),
        SymbolicExpression::Mul { x, y, degree_multiple: _ } =>
            cache_symbolic_expression_walk_binary(&x, &y, CachedBinaryOp::Mul, characteristic, cache),
    }
}

fn cache_symbolic_expression<F: Field>(
    x: &SymbolicExpression<F>,
    characteristic: Option<u32>
) -> HashMap<CachedSymbolicExpression, usize> {
    println!("Caching");
    println!("Calculating size:");
    println!("  {}", symbolic_expression_size(x));
    let mut cache = HashMap::new();
    let result = cache_symbolic_expression_walk(&x, characteristic, &mut cache);
    assert!(cache.len() - 1 == result, "Cache symbolic expression returned an index other than the last in the cache");
    cache
}

pub fn symbolic_expression_to_condensed_lean_string<F: Field>(
    x: &SymbolicExpression<F>,
    characteristic: Option<u32>,
) -> String {

    let cache = cache_symbolic_expression(x, characteristic)
        .into_iter()
        .sorted_by(|(_, l_id), (_, r_id)| {
            l_id.cmp(r_id)
        })
        .collect_vec();

    println!("Rendering");

    let let_exprs = cache
        .iter()
        .map(|(expr, idx)| match expr {
            CachedSymbolicExpression::Leaf(str) => format!("let x{idx} := {str}"),
            CachedSymbolicExpression::Neg(child) => format!("let x{idx} := -x{}", child),
            CachedSymbolicExpression::Binary { lhs, rhs, op } => match op {
                CachedBinaryOp::Add => format!("let x{idx} := x{} + x{}", lhs, rhs),
                CachedBinaryOp::Sub => format!("let x{idx} := x{} - x{}", lhs, rhs),
                CachedBinaryOp::Mul => format!("let x{idx} := x{} * x{}", lhs, rhs),
            },
        })
        .join("\n");

    let final_expr = format!("x{}", cache.len() - 1);

    format!("{let_exprs}\n{final_expr}")
    

    // let mut str = symbolic_expression_to_lean_string(x, characteristic);
    // println!("Getting leaves");
    // let leaves = get_symbolic_variable_leaf_string_set(x)
    //     .into_iter()
    //     .map(|leaf| symbolic_expression_to_lean_string(&leaf.0, None))
    //     .collect_vec();
    // println!("Got {}", leaves.len());
    // for (idx, leaf) in leaves.iter().enumerate() {
    //     println!("Leaf : {leaf}");
    //     str = str.replace(leaf, &format!("x{idx}"));
    // }
    // let params = leaves
    //     .iter()
    //     .enumerate()
    //     .map(|(idx, _)| format!("x{idx}"))
    //     .join(" ");
    // let function = format!(
    //     "(λ ({params} : F) => \n  {str}\n)",
    // );
    // let args = indent(leaves.iter().join("\n"), "  ");

    // format!("({function}\n{args}\n)")
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
    EF: Clone + Send + Sync,
{
    pub fn new(
        preprocessed_width: usize,
        width: usize,
        num_public_values: usize,
        num_challenges: usize,
    ) -> Self {
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
                (0..width)
                    .map(move |index| SymbolicVariable::new(Entry::Permutation { offset }, index))
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
    EF: Field,
{
    fn print_lean_base_constraints(&self) {
        println!("--Base constraints---");
        for (idx, constraint) in
            self
                .base_constraints
                .iter()
                .enumerate()
        {
            println!("Printing constraint {idx}");
            let constraint_text = format!(
                "  @[simp]\n  def constraint_{idx} {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) (row: ℕ) :=\n{} = 0\n",
                indent(symbolic_expression_to_lean_string(constraint, None), "    ")
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
                let multiplicity =
                    symbolic_expression_to_lean_string(&interaction.multiplicity, None);
                let data = format!(
                    "[{}]",
                    interaction
                        .data
                        .iter()
                        .map(|x| symbolic_expression_to_lean_string(x, None))
                        .join(", ")
                );
                format!("({multiplicity}, {data})")
            })
            .join(", ");

        println!("  @[simp]");
        println!(
            "  def constrain_interactions {{C : Type → Type → Type}} {{F ExtF : Type}} [Field F] [Field ExtF] [Circuit F ExtF C] (c : C F ExtF) :="
        );
        println!(
            "    Circuit.bus c = (List.range (Circuit.last_row c + 1)).flatMap (λ row => [{interactions_text}])"
        );
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
        ]
        .join("\n")
    }

    fn print_lean_constraint_simplification(&self) {
        println!("-----Constraint simplification------");
        for (idx, constraint) in self.base_constraints.iter().enumerate() {
            let constraint_text = format!(
                "{}",
                symbolic_expression_to_lean_string(constraint, None)
            );

            let simplified_constraint_text = [
                format!("@[NAME_constraint_and_interaction_simplification]"),
                format!("def constraint_{idx} (air : Valid_NAME F ExtF) (row : ℕ) : Prop :="),
                format!("  sorry"),
            ]
            .join("\n");

            let simplified_of_extracted = [
                format!("@[NAME_air_simplification]"),
                format!("lemma constraint_{idx}_of_extraction"),
                format!("    (air : Valid_NAME F ExtF) (row : ℕ)"),
                format!(
                    ": NAME.extraction.constraint_{idx} air row ↔ constraint_{idx} air row := by"
                ),
                Self::simplification_proof(),
            ]
            .join("\n");

            let output_text = format!("{simplified_constraint_text}\n\n{simplified_of_extracted}");

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
    F: Field,
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
where
    F: Field,
{
    type PublicVar = SymbolicVariable<F>;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F, EF, Challenge> PairBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
{
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F, EF, Challenge> ExtensionBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF>: Algebra<SymbolicExpression<F>>,
{
    type EF = EF;

    type ExprEF = SymbolicExpression<EF>;

    type VarEF = SymbolicVariable<EF>;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.extension_constraints.push(x.into())
    }
}

impl<F, EF, Challenge> PermutationAirBuilder for SymbolicAirBuilder<F, EF, Challenge>
where
    F: Field,
    EF: ExtensionField<F>,
    SymbolicExpression<EF>: Algebra<SymbolicExpression<F>>,
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

impl<F, EF, Challenge> InteractionAirBuilder for SymbolicAirBuilder<F, EF, Challenge>
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
