//! Emit the cross-validation data used by the manuscript figures, as two CSV
//! blocks on stdout:
//!
//! - `# eig`  (n, h, lambda1): the discrete first Dirichlet eigenvalue of
//!   `-Laplace` on the unit square at refinement `n`, converging to `2 pi^2`.
//! - `# conv` (n, h, error): the `H^1` seminorm error of the P1 solution of the
//!   manufactured problem, converging at first order.
//!
//! Run with `cargo run -q -p elliptic-fem --bin data`.

use elliptic_fem::convergence::unit_square_study;
use elliptic_fem::eig::first_dirichlet_eigenvalue;
use elliptic_fem::mesh::BoxMesh;

fn main() {
    println!("# eig");
    println!("n,h,lambda1");
    for n in [4usize, 6, 8, 10, 12, 16, 20, 24, 28] {
        let mesh = BoxMesh::unit_square(n);
        let l1 = first_dirichlet_eigenvalue(&mesh);
        println!("{n},{:.10},{:.10}", mesh.h(), l1);
    }

    println!("# conv");
    println!("n,h,error");
    let ns = [4usize, 8, 16, 32, 48];
    let conv = unit_square_study(&ns);
    for (n, s) in ns.iter().zip(conv.samples.iter()) {
        println!("{n},{:.10},{:.10}", s.h, s.error);
    }
    // The fitted rate is echoed as a comment for provenance.
    println!("# rate {:.6}", conv.rate);
}
