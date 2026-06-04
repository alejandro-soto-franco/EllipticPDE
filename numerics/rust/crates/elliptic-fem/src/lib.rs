//! Numerical cross-checks for the `elliptic-dirichlet` Lean formalisation.
//!
//! Keyed to `docs/superpowers/notes/constants.md`, the crate has two jobs:
//!
//! 1. **Analytic-estimate verification** ([`constants`], [`verify`]): compute the
//!    Poincare constant `C_P`, coercivity `alpha`, and continuity `beta` the Lean
//!    proof asserts on a box, and check they satisfy the required inequalities and
//!    dominate the sharp constant `1/sqrt(lambda_1)`.
//! 2. **FEM cross-check** ([`mesh`], [`assemble`], [`eig`], [`convergence`]): a P1
//!    finite-element Dirichlet solve on a box mesh from the `cartan-dec` stack,
//!    whose first eigenvalue matches the analytic `lambda_1` and whose `H^1`
//!    convergence rate matches the first-order a priori estimate.

pub mod assemble;
pub mod constants;
pub mod convergence;
pub mod eig;
pub mod ensemble;
pub mod mesh;
pub mod rng;
pub mod verify;
