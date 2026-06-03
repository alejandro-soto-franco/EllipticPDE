//! Analytic constants asserted by the Lean proof, computed in closed form.
//!
//! These mirror `docs/superpowers/notes/constants.md` (the authoritative list,
//! also reflected in `BilinearForm.lean`). For the divergence-form operator
//! `L u = -div(A grad u) + c u` with weak form
//! `B[u,v] = integral_Omega (A grad u . grad v + c u v)` on `H_0^1(Omega)`,
//! `A` uniformly elliptic with `A xi . xi >= lambda |xi|^2` and `|A| <= Lambda`,
//! and `0 <= c <= c_max`, the three constants are:
//!
//! * `C_P`, the Poincare constant: smallest `C` with
//!   `||u||_L2 <= C ||grad u||_L2` on `H_0^1(Omega)`;
//! * `alpha`, the coercivity constant: `B[u,u] >= alpha ||u||^2_{H_0^1}`;
//! * `beta`, the continuity constant: `|B[u,v]| <= beta ||u||_{H_0^1} ||v||_{H_0^1}`.
//!
//! The `H_0^1` norm is taken as `||grad .||_L2`, equivalent to the full norm by
//! Poincare, which is the convention under which `alpha = lambda`.

/// An axis-aligned box domain `Omega = prod_i (0, L_i)`, described by its side
/// lengths `L_i > 0`.
#[derive(Clone, Debug, PartialEq)]
pub struct BoxDomain {
    /// Side lengths, one per coordinate direction.
    pub sides: Vec<f64>,
}

impl BoxDomain {
    /// Construct a box from its side lengths. Panics if empty or any side is
    /// not strictly positive.
    pub fn new(sides: Vec<f64>) -> Self {
        assert!(!sides.is_empty(), "box must have at least one dimension");
        assert!(
            sides.iter().all(|&l| l > 0.0 && l.is_finite()),
            "side lengths must be finite and strictly positive"
        );
        Self { sides }
    }

    /// The `dim`-dimensional cube of side `side`.
    pub fn cube(dim: usize, side: f64) -> Self {
        Self::new(vec![side; dim])
    }

    /// The unit square `(0, 1)^2`.
    pub fn unit_square() -> Self {
        Self::cube(2, 1.0)
    }

    /// Spatial dimension `n`.
    pub fn dim(&self) -> usize {
        self.sides.len()
    }

    /// Euclidean diameter `sqrt(sum_i L_i^2)`.
    pub fn diameter(&self) -> f64 {
        self.sides.iter().map(|l| l * l).sum::<f64>().sqrt()
    }

    /// Largest side length.
    pub fn max_side(&self) -> f64 {
        self.sides.iter().copied().fold(f64::NEG_INFINITY, f64::max)
    }

    /// Smallest side length.
    pub fn min_side(&self) -> f64 {
        self.sides.iter().copied().fold(f64::INFINITY, f64::min)
    }
}

/// Coefficient data for `L u = -div(A grad u) + c u`: the ellipticity constant
/// `lambda` (`A xi . xi >= lambda |xi|^2`), the sup bound `Lambda` (`|A| <= Lambda`),
/// and `c_max` (`0 <= c <= c_max`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct EllipticData {
    /// Ellipticity constant `lambda > 0`.
    pub lambda: f64,
    /// Sup bound `Lambda >= lambda` on the coefficient matrix.
    pub lambda_sup: f64,
    /// Upper bound `c_max >= 0` on the zeroth-order coefficient.
    pub c_max: f64,
}

impl EllipticData {
    /// Construct coefficient data. Panics unless `0 < lambda <= Lambda` and
    /// `c_max >= 0`.
    pub fn new(lambda: f64, lambda_sup: f64, c_max: f64) -> Self {
        assert!(
            lambda > 0.0 && lambda.is_finite(),
            "lambda must be positive"
        );
        assert!(
            lambda_sup >= lambda && lambda_sup.is_finite(),
            "Lambda must be finite and at least lambda"
        );
        assert!(
            c_max >= 0.0 && c_max.is_finite(),
            "c_max must be nonnegative"
        );
        Self {
            lambda,
            lambda_sup,
            c_max,
        }
    }

    /// The Laplacian model problem `-div(grad u)`: `lambda = Lambda = 1`, `c = 0`.
    pub fn laplacian() -> Self {
        Self::new(1.0, 1.0, 0.0)
    }
}

/// The Poincare constant the Lean development actually delivers.
///
/// `slice_bound_euclBox` proves `||u||^2_L2 <= (L_i^2 / 2) ||d_i u||^2_L2` for
/// each direction `i`, and `poincare_testfn` averages the `d` directions under a
/// uniform slice constant `C = max_i (L_i^2 / 2) = max_side^2 / 2`, giving
/// `C_P^2 = C / d`. Hence
///
/// ```text
/// C_P = max_side / sqrt(2 * dim).
/// ```
///
/// For the unit square this is `1 / sqrt(4) = 0.5`.
pub fn c_p_lean(dom: &BoxDomain) -> f64 {
    let c = dom.max_side().powi(2) / 2.0;
    (c / dom.dim() as f64).sqrt()
}

/// The looser single-slice headline bound `C_P <= diam(Omega) / sqrt(2)`.
///
/// A single 1D Poincare step in any one direction gives
/// `C_P <= L_i / sqrt(2) <= diam(Omega) / sqrt(2)`. This is the bound named in
/// `constants.md`; [`c_p_lean`] is the sharper averaged constant the proof
/// assembles.
pub fn c_p_lean_diameter(dom: &BoxDomain) -> f64 {
    dom.diameter() / std::f64::consts::SQRT_2
}

/// Coercivity constant `alpha = lambda` (with the `H_0^1` norm taken as
/// `||grad .||_L2`).
pub fn alpha_lean(data: &EllipticData) -> f64 {
    data.lambda
}

/// Continuity constant `beta = Lambda + c_max * C_P^2`.
pub fn beta_lean(dom: &BoxDomain, data: &EllipticData) -> f64 {
    data.lambda_sup + data.c_max * c_p_lean(dom).powi(2)
}

/// The sharp Poincare constant `C_P = 1 / sqrt(lambda_1)` from the first
/// Dirichlet eigenvalue `lambda_1` of `-Laplace` on the domain.
pub fn c_p_sharp(lambda_1: f64) -> f64 {
    assert!(lambda_1 > 0.0, "the first Dirichlet eigenvalue is positive");
    1.0 / lambda_1.sqrt()
}

/// The exact first Dirichlet eigenvalue of `-Laplace` on the box
/// `prod_i (0, L_i)`: `lambda_1 = pi^2 sum_i 1 / L_i^2`, with eigenfunction
/// `prod_i sin(pi x_i / L_i)`.
pub fn dirichlet_eigenvalue_exact(dom: &BoxDomain) -> f64 {
    use std::f64::consts::PI;
    PI * PI * dom.sides.iter().map(|l| 1.0 / (l * l)).sum::<f64>()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn close(a: f64, b: f64) -> bool {
        (a - b).abs() <= 1e-12 * (1.0 + a.abs() + b.abs())
    }

    #[test]
    fn unit_square_geometry() {
        let dom = BoxDomain::unit_square();
        assert_eq!(dom.dim(), 2);
        assert!(close(dom.diameter(), std::f64::consts::SQRT_2));
        assert!(close(dom.max_side(), 1.0));
        assert!(close(dom.min_side(), 1.0));
    }

    #[test]
    fn c_p_lean_unit_square_is_half() {
        let dom = BoxDomain::unit_square();
        assert!(close(c_p_lean(&dom), 0.5));
        // The diameter headline is looser: sqrt(2) / sqrt(2) = 1.
        assert!(close(c_p_lean_diameter(&dom), 1.0));
        assert!(c_p_lean(&dom) <= c_p_lean_diameter(&dom));
    }

    #[test]
    fn lean_bound_dominates_sharp_on_unit_square() {
        let dom = BoxDomain::unit_square();
        let l1 = dirichlet_eigenvalue_exact(&dom); // 2 pi^2
        assert!(close(l1, 2.0 * std::f64::consts::PI.powi(2)));
        let sharp = c_p_sharp(l1); // 1 / (pi sqrt 2) ~ 0.2251
                                   // The proved Lean bound is a valid (over-)estimate of the sharp constant.
        assert!(c_p_lean(&dom) >= sharp);
        assert!(c_p_lean_diameter(&dom) >= sharp);
    }

    #[test]
    fn alpha_beta_laplacian() {
        let dom = BoxDomain::unit_square();
        let data = EllipticData::laplacian();
        assert!(close(alpha_lean(&data), 1.0));
        assert!(close(beta_lean(&dom, &data), 1.0)); // c_max = 0
        assert!(alpha_lean(&data) <= beta_lean(&dom, &data));
    }

    #[test]
    fn beta_grows_with_zeroth_order() {
        let dom = BoxDomain::unit_square();
        let data = EllipticData::new(1.0, 2.0, 4.0);
        // beta = Lambda + c_max C_P^2 = 2 + 4 * 0.25 = 3.
        assert!(close(beta_lean(&dom, &data), 3.0));
        assert!(alpha_lean(&data) <= beta_lean(&dom, &data));
    }

    #[test]
    fn elongated_box_constants() {
        let dom = BoxDomain::new(vec![2.0, 1.0]);
        // max_side = 2, C_P = 2 / sqrt(4) = 1.
        assert!(close(c_p_lean(&dom), 1.0));
        let l1 = dirichlet_eigenvalue_exact(&dom); // pi^2 (1/4 + 1)
        assert!(c_p_lean(&dom) >= c_p_sharp(l1));
    }
}
