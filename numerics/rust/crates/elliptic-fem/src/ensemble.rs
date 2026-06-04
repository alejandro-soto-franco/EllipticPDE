//! Mesh-ensemble runs: error bars from randomly perturbed meshes.
//!
//! The finite-element quantities are deterministic on a fixed mesh, so to attach
//! error bars we run each refinement on an ensemble of `k` randomly jittered
//! meshes (interior nodes displaced by a fraction of the cell size, boundary
//! fixed) and report the sample mean and standard deviation. The spread measures
//! sensitivity to mesh geometry; it is reproducible from a fixed seed.

use crate::convergence::{fit_rate, manufactured_h1_error, Sample};
use crate::eig::first_dirichlet_eigenvalue;
use crate::mesh::BoxMesh;
use crate::rng::SplitMix64;

/// Sample mean and (Bessel-corrected) standard deviation of an ensemble.
#[derive(Clone, Copy, Debug)]
pub struct Stat {
    /// Sample mean.
    pub mean: f64,
    /// Sample standard deviation.
    pub std: f64,
}

/// Mean and standard deviation of a slice (at least two samples).
pub fn stat(xs: &[f64]) -> Stat {
    let n = xs.len();
    assert!(n >= 2, "need at least two runs for a standard deviation");
    let mean = xs.iter().sum::<f64>() / n as f64;
    let var = xs.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n as f64 - 1.0);
    Stat {
        mean,
        std: var.sqrt(),
    }
}

/// One refinement level of the eigenvalue ensemble.
#[derive(Clone, Copy, Debug)]
pub struct EigEnsemble {
    /// Divisions per side.
    pub n: usize,
    /// Mesh size.
    pub h: f64,
    /// Discrete first Dirichlet eigenvalue across the ensemble.
    pub lambda1: Stat,
    /// Sharp Poincare constant `1/sqrt(lambda1)` across the ensemble.
    pub c_p: Stat,
}

/// The eigenvalue and sharp-`C_P` ensemble over `k` jittered meshes at each
/// refinement in `ns`.
pub fn eigenvalue_ensemble(
    ns: &[usize],
    jitter: f64,
    k: usize,
    rng: &mut SplitMix64,
) -> Vec<EigEnsemble> {
    ns.iter()
        .map(|&n| {
            let mut lams = Vec::with_capacity(k);
            let mut cps = Vec::with_capacity(k);
            let mut h = 0.0;
            for _ in 0..k {
                let mesh = BoxMesh::rectangle_jittered(1.0, 1.0, n, jitter, rng);
                h = mesh.h();
                let l1 = first_dirichlet_eigenvalue(&mesh);
                lams.push(l1);
                cps.push(1.0 / l1.sqrt());
            }
            EigEnsemble {
                n,
                h,
                lambda1: stat(&lams),
                c_p: stat(&cps),
            }
        })
        .collect()
}

/// One refinement level of the convergence ensemble.
#[derive(Clone, Copy, Debug)]
pub struct ConvEnsemble {
    /// Divisions per side.
    pub n: usize,
    /// Mesh size.
    pub h: f64,
    /// `H^1` seminorm error across the ensemble.
    pub error: Stat,
}

/// The convergence-error ensemble and the ensemble of fitted rates: `k`
/// independent jittered mesh sequences, each fitted to a first-order rate.
pub fn convergence_ensemble(
    ns: &[usize],
    jitter: f64,
    k: usize,
    rng: &mut SplitMix64,
) -> (Vec<ConvEnsemble>, Stat) {
    let mut errors: Vec<Vec<f64>> = vec![Vec::new(); ns.len()];
    let mut hs = vec![0.0; ns.len()];
    let mut rates = Vec::with_capacity(k);
    for _ in 0..k {
        let mut samples = Vec::with_capacity(ns.len());
        for (i, &n) in ns.iter().enumerate() {
            let mesh = BoxMesh::rectangle_jittered(1.0, 1.0, n, jitter, rng);
            hs[i] = mesh.h();
            let e = manufactured_h1_error(&mesh);
            errors[i].push(e);
            samples.push(Sample {
                h: mesh.h(),
                error: e,
            });
        }
        rates.push(fit_rate(&samples));
    }
    let per_level = ns
        .iter()
        .enumerate()
        .map(|(i, &n)| ConvEnsemble {
            n,
            h: hs[i],
            error: stat(&errors[i]),
        })
        .collect();
    (per_level, stat(&rates))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::c_p_lean;

    #[test]
    fn jittered_eigenvalue_brackets_exact() {
        let exact = 2.0 * std::f64::consts::PI.powi(2);
        let mut rng = SplitMix64::new(2024);
        let ens = eigenvalue_ensemble(&[12, 16], 0.2, 8, &mut rng);
        for e in &ens {
            // Each jittered mesh still over-estimates, and the spread is small.
            assert!(
                e.lambda1.mean >= exact - 1e-6,
                "mean {} below exact",
                e.lambda1.mean
            );
            assert!(e.lambda1.std > 0.0, "ensemble has spread");
            assert!(
                e.lambda1.std < 0.5 * e.lambda1.mean,
                "spread implausibly large"
            );
            // The sharp constant stays below the proved bound on every level.
            let dom = BoxMesh::unit_square(e.n).domain();
            assert!(e.c_p.mean <= c_p_lean(&dom));
        }
    }

    #[test]
    fn ensemble_rate_is_first_order() {
        let mut rng = SplitMix64::new(99);
        let (levels, rate) = convergence_ensemble(&[8, 16, 24], 0.2, 8, &mut rng);
        assert!((rate.mean - 1.0).abs() < 0.1, "rate mean {}", rate.mean);
        assert!(rate.std >= 0.0);
        for w in levels.windows(2) {
            assert!(w[1].error.mean < w[0].error.mean, "errors not decreasing");
        }
    }

    #[test]
    fn seed_makes_ensemble_reproducible() {
        let a = eigenvalue_ensemble(&[8], 0.2, 6, &mut SplitMix64::new(5));
        let b = eigenvalue_ensemble(&[8], 0.2, 6, &mut SplitMix64::new(5));
        assert_eq!(a[0].lambda1.mean, b[0].lambda1.mean);
        assert_eq!(a[0].lambda1.std, b[0].lambda1.std);
    }
}
