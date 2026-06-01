//! Numerical cross-checks for the `elliptic-dirichlet` Lean formalisation.
//!
//! Two jobs, both keyed to `docs/superpowers/notes/constants.md`:
//!
//! 1. Analytic-estimate verification: compute the Poincaré constant `C_P`, the
//!    coercivity constant `alpha`, and the continuity constant `beta` for a
//!    sample `(A, c)` on a box mesh, and check they satisfy the inequalities the
//!    Lean proof asserts.
//! 2. FEM cross-check: a P1 finite-element Dirichlet solve on a box mesh whose
//!    H^1 convergence rate matches the a priori estimate.
//!
//! Built on the `cartan` stack (cartan-dec, cartan-remesh). Wired at M7.

// TODO(M7): implement poincare_constant, coercivity, fem_solve.
