//! APIs for AIRs, and generalizations like PAIRs.

#![cfg_attr(not(feature = "extraction"), no_std)]

extern crate alloc;

mod air;
#[cfg(feature = "extraction")]
pub mod symbolic_builder;
#[cfg(feature = "extraction")]
pub mod symbolic_expression;
#[cfg(feature = "extraction")]
pub mod symbolic_variable;
pub mod utils;
mod virtual_column;

pub use air::*;
pub use virtual_column::*;
