//! Numerical cross-validation report for the `elliptic-dirichlet` formalisation.
//!
//! Runs the three checks of `constants.md` and prints a verdict:
//!
//! 1. structural inequalities on the analytic constants,
//! 2. the proved Poincare bound dominates the sharp FEM constant `1/sqrt(lambda_1)`,
//! 3. P1 `H^1` convergence at first order.
//!
//! Exits nonzero if any check fails. Run with `cargo run -p elliptic-fem --bin report`.

use elliptic_fem::constants::{dirichlet_eigenvalue_exact, BoxDomain, EllipticData};
use elliptic_fem::convergence::unit_square_study;
use elliptic_fem::eig::{dirichlet_spectrum, numeric_constants};
use elliptic_fem::mesh::BoxMesh;
use elliptic_fem::verify::{
    all_passed, lean_constants, rayleigh_checks, sharp_checks, structural_checks, Check,
};

fn print_checks(checks: &[Check]) -> bool {
    for c in checks {
        let mark = if c.passed { "PASS" } else { "FAIL" };
        println!(
            "    [{}] {}  ({:.6} vs {:.6})",
            mark, c.label, c.values.0, c.values.1
        );
    }
    all_passed(checks)
}

fn main() {
    let mut ok = true;

    println!("elliptic-dirichlet :: numerical cross-validation");
    println!("================================================\n");

    // 1. Analytic constants and their structural inequalities.
    println!("[1] Analytic constants (Lean side)");
    for dom in [BoxDomain::unit_square(), BoxDomain::new(vec![2.0, 1.0])] {
        let data = EllipticData::new(1.0, 2.0, 1.0);
        let k = lean_constants(&dom, &data);
        println!(
            "  box {:?}: C_P={:.4} (diam {:.4}), alpha={:.4}, beta={:.4}",
            dom.sides, k.c_p, k.c_p_diameter, k.alpha, k.beta
        );
        ok &= print_checks(&structural_checks(&dom, &data));
    }
    println!();

    // 2. Sharp Poincare constant from the FEM eigenproblem, vs the Lean bound
    //    and the exact analytic eigenvalue.
    println!("[2] Sharp Poincare constant (FEM eigenproblem on the unit square)");
    let n = 24;
    let mesh = BoxMesh::unit_square(n);
    let dom = mesh.domain();
    let data = EllipticData::new(1.0, 2.0, 1.0);
    let spec = dirichlet_spectrum(&mesh);
    let exact = dirichlet_eigenvalue_exact(&dom);
    let nc = numeric_constants(&spec, &data);
    println!(
        "  n={n}: lambda_1 numeric={:.4}, exact 2pi^2={:.4} (rel err {:.2e})",
        spec.mu_min,
        exact,
        (spec.mu_min - exact).abs() / exact
    );
    println!("  sharp C_P = 1/sqrt(lambda_1) = {:.4}", nc.c_p);
    ok &= print_checks(&sharp_checks(&dom, spec.mu_min));
    ok &= print_checks(&rayleigh_checks(&dom, &data, nc.alpha, nc.beta));
    println!();

    // 3. P1 H^1 convergence rate.
    println!("[3] P1 H^1 convergence (manufactured u = sin(pi x) sin(pi y))");
    let conv = unit_square_study(&[8, 16, 32]);
    for s in &conv.samples {
        println!("    h={:.4}  ||u-u_h||_H1={:.6}", s.h, s.error);
    }
    let rate_ok = (conv.rate - 1.0).abs() < 0.1;
    println!(
        "    [{}] fitted rate = {:.4} (expected 1)",
        if rate_ok { "PASS" } else { "FAIL" },
        conv.rate
    );
    ok &= rate_ok;

    println!("\n================================================");
    println!(
        "VERDICT: {}",
        if ok {
            "ALL CHECKS PASSED"
        } else {
            "FAILURES PRESENT"
        }
    );
    if !ok {
        std::process::exit(1);
    }
}
