//! APIs for AIRs, and generalizations like PAIRs.

// TODO build with no_std
// #![no_std]

extern crate alloc;

mod air;
pub mod logup;
pub mod symbolic_builder;
pub mod symbolic_expression;
pub mod symbolic_variable;
pub mod utils;
mod virtual_column;

pub use air::*;
pub use virtual_column::*;
