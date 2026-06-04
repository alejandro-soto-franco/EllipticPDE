//! Emit the cross-validation data used by the manuscript figures, as two CSV
//! blocks on stdout, each averaged over an ensemble of randomly jittered meshes
//! so the figures can carry error bars:
//!
//! - `# eig`  (n, h, lambda1_mean, lambda1_std, cp_mean, cp_std): the discrete
//!   first Dirichlet eigenvalue of `-Laplace` on the unit square and the sharp
//!   Poincare constant `1/sqrt(lambda1)`, converging to `2 pi^2` and `1/(pi sqrt2)`.
//! - `# conv` (n, h, error_mean, error_std): the `H^1` seminorm error of the P1
//!   solution of the manufactured problem, converging at first order.
//! - `# rate <mean> <std>`: the first-order rate fitted per realization.
//!
//! Run with `cargo run -q -p elliptic-fem --bin data`.

use elliptic_fem::ensemble::{convergence_ensemble, eigenvalue_ensemble};
use elliptic_fem::rng::SplitMix64;

/// Number of jittered meshes per refinement level.
const ENSEMBLE: usize = 12;
/// Interior-node displacement as a fraction of the cell size.
const JITTER: f64 = 0.25;
/// Fixed seed: the ensemble (and so the figures) is reproducible.
const SEED: u64 = 0xE111_DC0F_FEED_2024;

fn main() {
    let mut rng = SplitMix64::new(SEED);

    println!("# eig");
    println!("n,h,lambda1_mean,lambda1_std,cp_mean,cp_std");
    for e in eigenvalue_ensemble(&[4, 6, 8, 10, 12, 16, 20, 24], JITTER, ENSEMBLE, &mut rng) {
        println!(
            "{},{:.10},{:.10},{:.10},{:.10},{:.10}",
            e.n, e.h, e.lambda1.mean, e.lambda1.std, e.c_p.mean, e.c_p.std
        );
    }

    println!("# conv");
    println!("n,h,error_mean,error_std");
    let (levels, rate) = convergence_ensemble(&[4, 8, 16, 32], JITTER, ENSEMBLE, &mut rng);
    for c in &levels {
        println!(
            "{},{:.10},{:.10},{:.10}",
            c.n, c.h, c.error.mean, c.error.std
        );
    }
    println!("# rate {:.6} {:.6}", rate.mean, rate.std);
}
