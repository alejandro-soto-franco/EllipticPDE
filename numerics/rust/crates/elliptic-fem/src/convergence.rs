//! P1 convergence cross-check: the a priori estimate gives
//! `||u - u_h||_{H^1} <= C h` (first order). We solve a manufactured Dirichlet
//! problem on a sequence of meshes, measure the `H^1` seminorm error, and fit the
//! observed rate against `h`, confirming the exponent is `1` within tolerance.
//!
//! Manufactured solution on the unit square: `u = sin(pi x) sin(pi y)`, which
//! vanishes on the boundary and solves `-Laplace u = f` with `f = 2 pi^2 u`.

use crate::assemble::{
    nodal_values, restrict_interior, restrict_interior_vec, scatter_interior, stiffness_mass,
};
use crate::mesh::BoxMesh;
use nalgebra::DVector;
use std::f64::consts::PI;

/// Solve the P1 Galerkin Dirichlet problem `a(u_h, v) = (f, v)` on the mesh,
/// with the load integrated by the consistent mass (`(f, phi_i) ~ (M f_nodal)_i`).
/// Returns the full nodal solution, zero on the Dirichlet boundary.
pub fn solve_dirichlet(mesh: &BoxMesh, f: impl Fn([f64; 2]) -> f64) -> DVector<f64> {
    let (k, m) = stiffness_mass(mesh);
    let f_nodal = nodal_values(mesh, f);
    let load = &m * f_nodal;
    let ki = restrict_interior(&k, mesh);
    let bi = restrict_interior_vec(&load, mesh);
    let ui = ki.cholesky().expect("interior stiffness is SPD").solve(&bi);
    scatter_interior(&ui, mesh)
}

/// The `H^1` seminorm error `||grad(u - u_h)||_{L^2}`, with `grad u` supplied
/// analytically. `u_h` is the full nodal solution; its gradient is constant on
/// each triangle. Integrated by the three-point edge-midpoint rule (exact for
/// quadratics).
pub fn h1_seminorm_error(
    mesh: &BoxMesh,
    u_h: &DVector<f64>,
    grad_u: impl Fn([f64; 2]) -> [f64; 2],
) -> f64 {
    let mut err2 = 0.0;
    for t in 0..mesh.n_triangles() {
        let tri = mesh.triangle(t);
        let p = [
            mesh.vertex(tri[0]),
            mesh.vertex(tri[1]),
            mesh.vertex(tri[2]),
        ];
        let area = mesh.triangle_area(t);
        let b = [p[1][1] - p[2][1], p[2][1] - p[0][1], p[0][1] - p[1][1]];
        let c = [p[2][0] - p[1][0], p[0][0] - p[2][0], p[1][0] - p[0][0]];
        // Constant discrete gradient on this triangle.
        let mut gh = [0.0, 0.0];
        for a in 0..3 {
            let ua = u_h[tri[a]];
            gh[0] += ua * b[a] / (2.0 * area);
            gh[1] += ua * c[a] / (2.0 * area);
        }
        let mids = [
            [(p[0][0] + p[1][0]) * 0.5, (p[0][1] + p[1][1]) * 0.5],
            [(p[1][0] + p[2][0]) * 0.5, (p[1][1] + p[2][1]) * 0.5],
            [(p[2][0] + p[0][0]) * 0.5, (p[2][1] + p[0][1]) * 0.5],
        ];
        let mut cell = 0.0;
        for mid in mids {
            let g = grad_u(mid);
            cell += (g[0] - gh[0]).powi(2) + (g[1] - gh[1]).powi(2);
        }
        err2 += area / 3.0 * cell;
    }
    err2.sqrt()
}

/// One `(h, error)` sample of the convergence study.
#[derive(Clone, Copy, Debug)]
pub struct Sample {
    /// Mesh size.
    pub h: f64,
    /// `H^1` seminorm error.
    pub error: f64,
}

/// The result of a convergence study: the per-mesh samples and the fitted rate.
#[derive(Clone, Debug)]
pub struct Convergence {
    /// `(h, error)` per refinement level.
    pub samples: Vec<Sample>,
    /// Least-squares slope of `log(error)` against `log(h)` (the observed order).
    pub rate: f64,
}

/// Run the manufactured-solution convergence study on the unit square over the
/// given refinement levels `ns` (divisions per side).
pub fn unit_square_study(ns: &[usize]) -> Convergence {
    let u_exact = |x: [f64; 2]| (PI * x[0]).sin() * (PI * x[1]).sin();
    let grad_u = |x: [f64; 2]| {
        [
            PI * (PI * x[0]).cos() * (PI * x[1]).sin(),
            PI * (PI * x[0]).sin() * (PI * x[1]).cos(),
        ]
    };
    let f = move |x: [f64; 2]| 2.0 * PI * PI * u_exact(x);

    let mut samples = Vec::new();
    for &n in ns {
        let mesh = BoxMesh::unit_square(n);
        let u_h = solve_dirichlet(&mesh, f);
        samples.push(Sample {
            h: mesh.h(),
            error: h1_seminorm_error(&mesh, &u_h, grad_u),
        });
    }
    let rate = fit_rate(&samples);
    Convergence { samples, rate }
}

/// Least-squares slope of `log(error)` against `log(h)`.
pub fn fit_rate(samples: &[Sample]) -> f64 {
    let n = samples.len() as f64;
    let xs: Vec<f64> = samples.iter().map(|s| s.h.ln()).collect();
    let ys: Vec<f64> = samples.iter().map(|s| s.error.ln()).collect();
    let mx = xs.iter().sum::<f64>() / n;
    let my = ys.iter().sum::<f64>() / n;
    let sxy: f64 = xs.iter().zip(&ys).map(|(x, y)| (x - mx) * (y - my)).sum();
    let sxx: f64 = xs.iter().map(|x| (x - mx).powi(2)).sum();
    sxy / sxx
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_solution_is_recovered_approximately() {
        // The discrete solution is O(h) close in H^1; the seminorm of u itself is
        // ||grad u|| = pi / sqrt(2) ~ 2.22, so the error constant is ~3.5.
        let conv = unit_square_study(&[8, 16]);
        for s in &conv.samples {
            assert!(
                s.error < 4.0 * s.h,
                "error {} not O(h) at h={}",
                s.error,
                s.h
            );
        }
    }

    #[test]
    fn first_order_h1_convergence() {
        let conv = unit_square_study(&[8, 16, 32]);
        // First-order method: the fitted rate is 1 within tolerance.
        assert!(
            (conv.rate - 1.0).abs() < 0.1,
            "fitted H^1 rate {} not first order; samples {:?}",
            conv.rate,
            conv.samples
        );
    }

    #[test]
    fn error_decreases_monotonically() {
        let conv = unit_square_study(&[4, 8, 16]);
        for w in conv.samples.windows(2) {
            assert!(
                w[1].error < w[0].error,
                "error not decreasing: {:?}",
                conv.samples
            );
        }
    }
}
