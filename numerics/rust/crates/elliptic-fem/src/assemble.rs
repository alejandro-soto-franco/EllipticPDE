//! P1 (linear Lagrange) finite-element assembly on a [`BoxMesh`].
//!
//! For each triangle with vertices `p0, p1, p2` and area `A`, the barycentric
//! basis gradients are constant, `grad phi_i = (b_i, c_i) / (2A)` with
//! `b = (y1-y2, y2-y0, y0-y1)`, `c = (x2-x1, x0-x2, x1-x0)`. The local stiffness
//! is `Ke[i][j] = (b_i b_j + c_i c_j) / (4A)` and the local consistent mass is
//! `Me[i][j] = (A/12)(2 if i==j else 1)`. These are assembled into the global
//! `K` (stiffness, the `H^1` seminorm Gram matrix) and `M` (mass, the `L^2` Gram
//! matrix) over all vertices; [`restrict_interior`] drops the Dirichlet
//! boundary rows and columns.

use crate::mesh::BoxMesh;
use nalgebra::{DMatrix, DVector};

/// Assemble the global P1 stiffness `K` and consistent mass `M` over every
/// vertex of the mesh. `K` is the `L^2` Gram matrix of the gradients (the `H^1`
/// seminorm), `M` the `L^2` Gram matrix of the basis functions.
pub fn stiffness_mass(mesh: &BoxMesh) -> (DMatrix<f64>, DMatrix<f64>) {
    let n = mesh.n_vertices();
    let mut k = DMatrix::<f64>::zeros(n, n);
    let mut m = DMatrix::<f64>::zeros(n, n);
    for t in 0..mesh.n_triangles() {
        let tri = mesh.triangle(t);
        let p: [[f64; 2]; 3] = [
            mesh.vertex(tri[0]),
            mesh.vertex(tri[1]),
            mesh.vertex(tri[2]),
        ];
        let area = mesh.triangle_area(t);
        // Gradient coefficients of the barycentric basis.
        let b = [p[1][1] - p[2][1], p[2][1] - p[0][1], p[0][1] - p[1][1]];
        let c = [p[2][0] - p[1][0], p[0][0] - p[2][0], p[1][0] - p[0][0]];
        for a in 0..3 {
            for d in 0..3 {
                let ke = (b[a] * b[d] + c[a] * c[d]) / (4.0 * area);
                let me = area / 12.0 * if a == d { 2.0 } else { 1.0 };
                k[(tri[a], tri[d])] += ke;
                m[(tri[a], tri[d])] += me;
            }
        }
    }
    (k, m)
}

/// Restrict a global vertex matrix to the interior (free) degrees of freedom,
/// dropping rows and columns of Dirichlet boundary vertices.
pub fn restrict_interior(full: &DMatrix<f64>, mesh: &BoxMesh) -> DMatrix<f64> {
    let interior = mesh.interior_vertices();
    let n = interior.len();
    let mut out = DMatrix::<f64>::zeros(n, n);
    for (a, &ga) in interior.iter().enumerate() {
        for (d, &gd) in interior.iter().enumerate() {
            out[(a, d)] = full[(ga, gd)];
        }
    }
    out
}

/// Restrict a global vertex vector to the interior degrees of freedom.
pub fn restrict_interior_vec(full: &DVector<f64>, mesh: &BoxMesh) -> DVector<f64> {
    let interior = mesh.interior_vertices();
    DVector::from_iterator(interior.len(), interior.iter().map(|&g| full[g]))
}

/// Scatter an interior-only vector back to a full vertex vector, with zeros on
/// the Dirichlet boundary.
pub fn scatter_interior(interior_vec: &DVector<f64>, mesh: &BoxMesh) -> DVector<f64> {
    let interior = mesh.interior_vertices();
    let mut out = DVector::<f64>::zeros(mesh.n_vertices());
    for (a, &g) in interior.iter().enumerate() {
        out[g] = interior_vec[a];
    }
    out
}

/// Sample a function at every vertex of the mesh.
pub fn nodal_values(mesh: &BoxMesh, f: impl Fn([f64; 2]) -> f64) -> DVector<f64> {
    DVector::from_iterator(
        mesh.n_vertices(),
        (0..mesh.n_vertices()).map(|i| f(mesh.vertex(i))),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stiffness_annihilates_constants() {
        // K * 1 = 0: the gradient of a constant is zero.
        let mesh = BoxMesh::unit_square(4);
        let (k, _m) = stiffness_mass(&mesh);
        let ones = DVector::from_element(mesh.n_vertices(), 1.0);
        let kv = &k * ones;
        assert!(kv.amax() < 1e-12, "K*1 max = {}", kv.amax());
    }

    #[test]
    fn mass_row_sums_to_total_area() {
        // Rows of the consistent mass sum to the integral of phi_i; the grand
        // total is the area of the domain.
        let mesh = BoxMesh::rectangle(2.0, 3.0, 5);
        let (_k, m) = stiffness_mass(&mesh);
        let total: f64 = m.sum();
        assert!((total - 6.0).abs() < 1e-12, "sum M = {total}");
    }

    #[test]
    fn matrices_symmetric() {
        let mesh = BoxMesh::unit_square(6);
        let (k, m) = stiffness_mass(&mesh);
        assert!((&k - k.transpose()).amax() < 1e-14);
        assert!((&m - m.transpose()).amax() < 1e-14);
    }

    #[test]
    fn restriction_sizes() {
        let mesh = BoxMesh::unit_square(5);
        let (k, _m) = stiffness_mass(&mesh);
        let ki = restrict_interior(&k, &mesh);
        assert_eq!(ki.nrows(), 16); // 4x4 interior
        assert_eq!(ki.ncols(), 16);
    }
}
