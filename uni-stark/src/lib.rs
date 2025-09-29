//! A minimal univariate STARK framework.

#![no_std]

extern crate alloc;

mod config;
mod folder;
mod proof;
mod prover;
mod symbolic_builder;
mod verifier;

mod check_constraints;

pub use check_constraints::*;
pub use config::*;
pub use folder::*;
pub use proof::*;
pub use prover::*;
pub use symbolic_builder::*;
pub use verifier::*;
