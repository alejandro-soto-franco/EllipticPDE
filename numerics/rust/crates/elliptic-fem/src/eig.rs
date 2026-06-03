//! The Dirichlet generalised eigenproblem `K x = mu M x` on the interior degrees
//! of freedom, and the numeric constants read off its spectrum.
//!
//! The smallest generalised eigenvalue `mu_min` is the discrete first Dirichlet
//! eigenvalue `lambda_1` of `-Laplace`; the sharp Poincare constant is
//! `1/sqrt(mu_min)`. For an isotropic sample `A = lambda I`, `0 <= c <= c_max`,
//! the Rayleigh quotient `B[u,u]/||grad u||^2 = lambda + c (x^T M x)/(x^T K x)`
//! ranges over `[lambda + c/mu_max, lambda + c/mu_min]`, giving the numeric
//! coercivity and continuity constants.
//!
//! `M` is the consistent (SPD) mass matrix, so we reduce to a standard symmetric
//! eigenproblem by the Cholesky factor of `M`.

use crate::assemble::{restrict_interior, stiffness_mass};
use crate::constants::EllipticData;
use crate::mesh::BoxMesh;

/// The extremal generalised eigenvalues of `K x = mu M x` on the interior.
#[derive(Clone, Copy, Debug)]
pub struct Spectrum {
    /// Smallest generalised eigenvalue = discrete first Dirichlet eigenvalue.
    pub mu_min: f64,
    /// Largest generalised eigenvalue (mesh-dependent, scales like `1/h^2`).
    pub mu_max: f64,
}

/// Solve the Dirichlet generalised eigenproblem `K x = mu M x` on the interior
/// DOFs of the mesh and return its extremal eigenvalues.
pub fn dirichlet_spectrum(mesh: &BoxMesh) -> Spectrum {
    let (k, m) = stiffness_mass(mesh);
    let ki = restrict_interior(&k, mesh);
    let mi = restrict_interior(&m, mesh);
    // Reduce K x = mu M x to the standard symmetric problem C y = mu y with
    // C = L^{-1} K L^{-T}, where M = L L^T.
    let chol = mi.clone().cholesky().expect("interior mass matrix is SPD");
    let linv = chol
        .l()
        .try_inverse()
        .expect("Cholesky factor is invertible");
    let c = &linv * &ki * linv.transpose();
    // Symmetrise to kill rounding asymmetry before the symmetric solver.
    let c = (&c + c.transpose()) * 0.5;
    let evals = c.symmetric_eigen().eigenvalues;
    let mu_min = evals.iter().copied().fold(f64::INFINITY, f64::min);
    let mu_max = evals.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    Spectrum { mu_min, mu_max }
}

/// The discrete first Dirichlet eigenvalue `lambda_1` of `-Laplace` on the mesh.
pub fn first_dirichlet_eigenvalue(mesh: &BoxMesh) -> f64 {
    dirichlet_spectrum(mesh).mu_min
}

/// The sharp numeric Poincare constant `1/sqrt(lambda_1)` from the mesh.
pub fn c_p_numeric(mesh: &BoxMesh) -> f64 {
    1.0 / first_dirichlet_eigenvalue(mesh).sqrt()
}

/// Numeric coercivity and continuity constants for the isotropic sample
/// `A = lambda I`, `c = c_max`, read off the spectrum:
/// `alpha = lambda + c/mu_max`, `beta = lambda + c/mu_min`.
#[derive(Clone, Copy, Debug)]
pub struct NumericConstants {
    /// Sharp Poincare constant `1/sqrt(mu_min)`.
    pub c_p: f64,
    /// Numeric coercivity `lambda + c/mu_max`.
    pub alpha: f64,
    /// Numeric continuity `lambda + c/mu_min`.
    pub beta: f64,
}

/// Read the numeric constants off the spectrum for a coefficient sample.
pub fn numeric_constants(spec: &Spectrum, data: &EllipticData) -> NumericConstants {
    NumericConstants {
        c_p: 1.0 / spec.mu_min.sqrt(),
        alpha: data.lambda + data.c_max / spec.mu_max,
        beta: data.lambda + data.c_max / spec.mu_min,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::dirichlet_eigenvalue_exact;

    #[test]
    fn first_eigenvalue_approximates_two_pi_squared() {
        let exact = dirichlet_eigenvalue_exact(&BoxMesh::unit_square(16).domain());
        let mesh = BoxMesh::unit_square(16);
        let mu = first_dirichlet_eigenvalue(&mesh);
        // P1 over-estimates eigenvalues; the discrete value sits just above 2 pi^2.
        assert!(mu >= exact - 1e-6, "mu {mu} below exact {exact}");
        assert!(mu <= exact * 1.05, "mu {mu} too far above exact {exact}");
    }

    #[test]
    fn eigenvalue_converges_with_refinement() {
        let exact = 2.0 * std::f64::consts::PI.powi(2);
        let e6 = (first_dirichlet_eigenvalue(&BoxMesh::unit_square(6)) - exact).abs();
        let e10 = (first_dirichlet_eigenvalue(&BoxMesh::unit_square(10)) - exact).abs();
        let e16 = (first_dirichlet_eigenvalue(&BoxMesh::unit_square(16)) - exact).abs();
        assert!(
            e10 < e6 && e16 < e10,
            "errors not decreasing: {e6} {e10} {e16}"
        );
    }

    #[test]
    fn sharp_constant_below_lean_bound() {
        use crate::constants::c_p_lean;
        let mesh = BoxMesh::unit_square(16);
        let dom = mesh.domain();
        assert!(c_p_numeric(&mesh) <= c_p_lean(&dom));
    }

    #[test]
    fn numeric_constants_bracket_lambda() {
        let mesh = BoxMesh::unit_square(12);
        let spec = dirichlet_spectrum(&mesh);
        let data = EllipticData::new(1.0, 2.0, 1.0);
        let nc = numeric_constants(&spec, &data);
        assert!(nc.alpha >= data.lambda - 1e-12);
        assert!(nc.beta >= nc.alpha);
    }
}
