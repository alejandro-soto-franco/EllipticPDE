//! Box meshes from the `cartan-dec` stack.
//!
//! `cartan-dec` provides `FlatMesh::unit_square_grid`; we scale its `[0,1]^2`
//! grid to a general rectangle `(0, Lx) x (0, Ly)` and track which vertices lie
//! on the Dirichlet boundary. The mesh, its triangle connectivity, and triangle
//! areas all come from `cartan-dec`; the P1 assembly in [`crate::assemble`] reads
//! this geometry.

use crate::constants::BoxDomain;
use crate::rng::SplitMix64;
use cartan_dec::mesh::FlatMesh;

/// A uniform triangulation of the rectangle `(0, Lx) x (0, Ly)` with `n`
/// divisions per side (so `2 n^2` triangles and `(n+1)^2` vertices), built by
/// scaling `cartan-dec`'s unit-square grid.
pub struct BoxMesh {
    /// The underlying `cartan-dec` simplicial complex.
    pub mesh: FlatMesh,
    /// Side lengths `[Lx, Ly]`.
    pub sides: [f64; 2],
    /// Divisions per side.
    pub n: usize,
    /// Per-vertex flag: `true` if the vertex lies on the box boundary.
    boundary: Vec<bool>,
}

impl BoxMesh {
    /// A scaled grid on `(0, Lx) x (0, Ly)` with `n` divisions per side.
    pub fn rectangle(lx: f64, ly: f64, n: usize) -> Self {
        assert!(n >= 1, "mesh needs at least one division");
        assert!(lx > 0.0 && ly > 0.0, "side lengths must be positive");
        let mut vertices: Vec<[f64; 2]> = Vec::with_capacity((n + 1) * (n + 1));
        let mut boundary: Vec<bool> = Vec::with_capacity((n + 1) * (n + 1));
        for j in 0..=n {
            for i in 0..=n {
                vertices.push([i as f64 / n as f64 * lx, j as f64 / n as f64 * ly]);
                boundary.push(i == 0 || i == n || j == 0 || j == n);
            }
        }
        let idx = |i: usize, j: usize| j * (n + 1) + i;
        let mut triangles: Vec<[usize; 3]> = Vec::with_capacity(2 * n * n);
        for j in 0..n {
            for i in 0..n {
                let (v00, v10, v01, v11) =
                    (idx(i, j), idx(i + 1, j), idx(i, j + 1), idx(i + 1, j + 1));
                triangles.push([v00, v10, v01]);
                triangles.push([v10, v11, v01]);
            }
        }
        Self {
            mesh: FlatMesh::from_triangles(vertices, triangles),
            sides: [lx, ly],
            n,
            boundary,
        }
    }

    /// The unit square `(0, 1)^2` with `n` divisions per side.
    pub fn unit_square(n: usize) -> Self {
        Self::rectangle(1.0, 1.0, n)
    }

    /// A grid on `(0, Lx) x (0, Ly)` whose interior vertices are randomly
    /// displaced by up to `jitter_frac` of the cell size in each axis; boundary
    /// vertices stay fixed so the domain shape and the Dirichlet condition are
    /// preserved. Used to build a mesh ensemble for error bars on the otherwise
    /// deterministic finite-element quantities.
    pub fn rectangle_jittered(
        lx: f64,
        ly: f64,
        n: usize,
        jitter_frac: f64,
        rng: &mut SplitMix64,
    ) -> Self {
        assert!(n >= 1, "mesh needs at least one division");
        assert!(lx > 0.0 && ly > 0.0, "side lengths must be positive");
        assert!(
            (0.0..0.5).contains(&jitter_frac),
            "jitter must stay below half a cell"
        );
        let (amp_x, amp_y) = (jitter_frac * lx / n as f64, jitter_frac * ly / n as f64);
        let mut vertices: Vec<[f64; 2]> = Vec::with_capacity((n + 1) * (n + 1));
        let mut boundary: Vec<bool> = Vec::with_capacity((n + 1) * (n + 1));
        for j in 0..=n {
            for i in 0..=n {
                let on_bd = i == 0 || i == n || j == 0 || j == n;
                let mut x = i as f64 / n as f64 * lx;
                let mut y = j as f64 / n as f64 * ly;
                if !on_bd {
                    x += amp_x * rng.next_signed();
                    y += amp_y * rng.next_signed();
                }
                vertices.push([x, y]);
                boundary.push(on_bd);
            }
        }
        let idx = |i: usize, j: usize| j * (n + 1) + i;
        let mut triangles: Vec<[usize; 3]> = Vec::with_capacity(2 * n * n);
        for j in 0..n {
            for i in 0..n {
                let (v00, v10, v01, v11) =
                    (idx(i, j), idx(i + 1, j), idx(i, j + 1), idx(i + 1, j + 1));
                triangles.push([v00, v10, v01]);
                triangles.push([v10, v11, v01]);
            }
        }
        Self {
            mesh: FlatMesh::from_triangles(vertices, triangles),
            sides: [lx, ly],
            n,
            boundary,
        }
    }

    /// Number of vertices `(n+1)^2`.
    pub fn n_vertices(&self) -> usize {
        self.mesh.n_vertices()
    }

    /// Number of triangles `2 n^2`.
    pub fn n_triangles(&self) -> usize {
        self.mesh.n_simplices()
    }

    /// The three vertex indices of triangle `t`.
    pub fn triangle(&self, t: usize) -> [usize; 3] {
        self.mesh.simplices[t]
    }

    /// The position of vertex `i`.
    pub fn vertex(&self, i: usize) -> [f64; 2] {
        let v = self.mesh.vertex(i);
        [v.x, v.y]
    }

    /// The area of triangle `t` (from `cartan-dec`).
    pub fn triangle_area(&self, t: usize) -> f64 {
        self.mesh.triangle_area_flat(t)
    }

    /// Whether vertex `i` is on the Dirichlet boundary.
    pub fn is_boundary(&self, i: usize) -> bool {
        self.boundary[i]
    }

    /// The interior (free) vertex indices, in increasing order.
    pub fn interior_vertices(&self) -> Vec<usize> {
        (0..self.n_vertices())
            .filter(|&i| !self.is_boundary(i))
            .collect()
    }

    /// Mesh size `h`: the longer cell side `max(Lx, Ly) / n`.
    pub fn h(&self) -> f64 {
        self.sides[0].max(self.sides[1]) / self.n as f64
    }

    /// The continuous box domain this mesh discretises.
    pub fn domain(&self) -> BoxDomain {
        BoxDomain::new(vec![self.sides[0], self.sides[1]])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_and_boundary() {
        let m = BoxMesh::unit_square(4);
        assert_eq!(m.n_vertices(), 25);
        assert_eq!(m.n_triangles(), 32);
        // Interior of a 4x4 grid is a 3x3 block of vertices.
        assert_eq!(m.interior_vertices().len(), 9);
        // Corner (0,0) is on the boundary; centre (2,2) -> index 12 is interior.
        assert!(m.is_boundary(0));
        assert!(!m.is_boundary(12));
    }

    #[test]
    fn total_area_matches_rectangle() {
        let m = BoxMesh::rectangle(2.0, 3.0, 5);
        let total: f64 = (0..m.n_triangles()).map(|t| m.triangle_area(t)).sum();
        assert!((total - 6.0).abs() < 1e-12, "total area {total}");
    }

    #[test]
    fn h_is_cell_size() {
        let m = BoxMesh::unit_square(8);
        assert!((m.h() - 0.125).abs() < 1e-15);
    }
}
