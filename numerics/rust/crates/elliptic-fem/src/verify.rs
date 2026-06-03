//! Cross-validation of the analytic constants against the inequalities the Lean
//! proof asserts, and against a numeric first Dirichlet eigenvalue.
//!
//! The numeric `lambda_1` may come from the exact box formula
//! ([`crate::constants::dirichlet_eigenvalue_exact`]) or from the assembled FEM
//! generalised eigenproblem ([`crate::eig`]). Either way the headline check is
//! `C_P^Lean >= 1 / sqrt(lambda_1)`: the proved bound is a valid over-estimate of
//! the sharp constant.

use crate::constants::{
    alpha_lean, beta_lean, c_p_lean, c_p_lean_diameter, c_p_sharp, BoxDomain, EllipticData,
};

/// The Lean-side constants for a given box and coefficient data.
#[derive(Clone, Copy, Debug)]
pub struct LeanConstants {
    /// Averaged Poincare constant `max_side / sqrt(2 dim)`.
    pub c_p: f64,
    /// Looser diameter headline `diam / sqrt(2)`.
    pub c_p_diameter: f64,
    /// Coercivity constant `alpha = lambda`.
    pub alpha: f64,
    /// Continuity constant `beta = Lambda + c_max C_P^2`.
    pub beta: f64,
}

/// Assemble the Lean-side constants.
pub fn lean_constants(dom: &BoxDomain, data: &EllipticData) -> LeanConstants {
    LeanConstants {
        c_p: c_p_lean(dom),
        c_p_diameter: c_p_lean_diameter(dom),
        alpha: alpha_lean(data),
        beta: beta_lean(dom, data),
    }
}

/// The outcome of one structural check, carrying a human-readable label so a
/// report can list exactly what was verified.
#[derive(Clone, Debug)]
pub struct Check {
    /// What the check asserts.
    pub label: String,
    /// Whether it passed.
    pub passed: bool,
    /// The two compared quantities (left, right) for reporting.
    pub values: (f64, f64),
}

impl Check {
    fn le(label: &str, left: f64, right: f64) -> Self {
        Self {
            label: label.to_string(),
            passed: left <= right + Self::TOL,
            values: (left, right),
        }
    }

    fn lt(label: &str, left: f64, right: f64) -> Self {
        Self {
            label: label.to_string(),
            passed: left < right + Self::TOL,
            values: (left, right),
        }
    }

    fn gt(label: &str, left: f64, right: f64) -> Self {
        Self {
            label: label.to_string(),
            passed: left > right - Self::TOL,
            values: (left, right),
        }
    }

    const TOL: f64 = 1e-9;
}

/// The structural inequalities that the weak theory requires, independent of any
/// numerics: coercivity is positive, coercivity does not exceed continuity, the
/// Poincare constant is positive, and the averaged bound is no looser than the
/// diameter headline.
pub fn structural_checks(dom: &BoxDomain, data: &EllipticData) -> Vec<Check> {
    let k = lean_constants(dom, data);
    vec![
        Check::gt("alpha > 0 (coercive)", k.alpha, 0.0),
        Check::le("alpha <= beta (coercivity <= continuity)", k.alpha, k.beta),
        Check::gt("C_P > 0", k.c_p, 0.0),
        Check::le("C_P (averaged) <= C_P (diameter)", k.c_p, k.c_p_diameter),
    ]
}

/// The cross-check against a numeric first Dirichlet eigenvalue `lambda_1`:
/// every proved Poincare bound must dominate the sharp constant `1/sqrt(lambda_1)`.
pub fn sharp_checks(dom: &BoxDomain, lambda_1: f64) -> Vec<Check> {
    let sharp = c_p_sharp(lambda_1);
    vec![
        Check::gt(
            "C_P^Lean (averaged) >= 1/sqrt(lambda_1)",
            c_p_lean(dom),
            sharp,
        ),
        Check::gt(
            "C_P^Lean (diameter) >= 1/sqrt(lambda_1)",
            c_p_lean_diameter(dom),
            sharp,
        ),
    ]
}

/// The continuity/coercivity cross-check against the numeric extremal Rayleigh
/// quotients of the assembled form. For isotropic `A = lambda I`, the smallest
/// and largest Rayleigh quotients of `B[u,u] / ||grad u||^2` are
/// `lambda + c * nu_min` and `lambda + c * nu_max`, where `nu = ||u||^2_L2 / ||grad u||^2`
/// ranges in `[1/lambda_max, 1/lambda_min]` over the eigenproblem
/// `K x = lambda M x`. The proved `alpha` is a lower bound and `beta` an upper
/// bound for these.
pub fn rayleigh_checks(
    dom: &BoxDomain,
    data: &EllipticData,
    alpha_numeric: f64,
    beta_numeric: f64,
) -> Vec<Check> {
    let k = lean_constants(dom, data);
    vec![
        Check::le(
            "alpha^Lean <= alpha^numeric (coercivity is achieved)",
            k.alpha,
            alpha_numeric,
        ),
        Check::gt(
            "beta^Lean >= beta^numeric (continuity is achieved)",
            k.beta,
            beta_numeric,
        ),
        Check::lt("alpha^numeric <= beta^numeric", alpha_numeric, beta_numeric),
    ]
}

/// True iff every check in the slice passed.
pub fn all_passed(checks: &[Check]) -> bool {
    checks.iter().all(|c| c.passed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::dirichlet_eigenvalue_exact;

    #[test]
    fn structural_holds_for_samples() {
        for dom in [
            BoxDomain::unit_square(),
            BoxDomain::new(vec![2.0, 1.0]),
            BoxDomain::cube(3, 1.5),
        ] {
            for data in [EllipticData::laplacian(), EllipticData::new(0.5, 3.0, 2.0)] {
                assert!(
                    all_passed(&structural_checks(&dom, &data)),
                    "{dom:?} {data:?}"
                );
            }
        }
    }

    #[test]
    fn sharp_check_against_exact_eigenvalue() {
        for dom in [
            BoxDomain::unit_square(),
            BoxDomain::new(vec![3.0, 1.0, 2.0]),
        ] {
            let l1 = dirichlet_eigenvalue_exact(&dom);
            assert!(all_passed(&sharp_checks(&dom, l1)), "{dom:?}");
        }
    }

    #[test]
    fn rayleigh_holds_for_isotropic_sample() {
        let dom = BoxDomain::unit_square();
        let data = EllipticData::new(1.0, 2.0, 1.0);
        let l1 = dirichlet_eigenvalue_exact(&dom);
        let c_p_sharp_sq = c_p_sharp(l1).powi(2);
        // alpha^numeric = lambda + c * nu_min >= lambda; beta^numeric = lambda + c * C_P_sharp^2.
        let alpha_numeric = data.lambda; // nu_min ~ 0 lower bound for this isotropic test
        let beta_numeric = data.lambda + data.c_max * c_p_sharp_sq;
        assert!(all_passed(&rayleigh_checks(
            &dom,
            &data,
            alpha_numeric,
            beta_numeric
        )));
    }
}
