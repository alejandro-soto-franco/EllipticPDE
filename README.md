# elliptic-dirichlet

A machine-verified existence and uniqueness theorem, in Lean 4, for the weak
solution of the Dirichlet problem for a uniformly elliptic, divergence-form
linear operator on a bounded domain:

$$-\operatorname{div}(A\nabla u) + c\,u = f \ \text{ in } \Omega, \qquad u = 0 \ \text{ on } \partial\Omega,$$

with $A$ uniformly elliptic with bounded measurable coefficients and $c\ge 0$.
The weak formulation seeks $u\in H_0^1(\Omega)$ with $B[u,v]=\langle f,v\rangle$
for all $v\in H_0^1(\Omega)$, where $B[u,v]=\int_\Omega A\nabla u\cdot\nabla v + c\,uv$.

The proof follows the functional-analysis route: a Sobolev layer, the Poincaré
inequality, and the Lax-Milgram theorem, with a Fredholm-alternative
generalisation as the next milestone.

Authors: Alejandro José Soto Franco and Kobe Marshall-Stevens.

## Three tracks

| Track | Tool | Contents |
|-------|------|----------|
| Formal | Lean 4 + Mathlib | `lean/` typed statements and proofs |
| Theory | LaTeX (kms-latex) + SymPy | `latex/` manuscript, `numerics/python/` symbolic checks |
| Numerics | Rust (cartan stack) | `numerics/rust/` FEM cross-check and constant verification |

## Layout

- `lean/` standalone lake project pinned to Lean `v4.31.0-rc1`, depending on
  Mathlib through the shared `mathlib4-fork-stable` worktree. Build artefacts
  live under `/home/lean-caches/elliptic-dirichlet` via the `.lake` symlink.
- `latex/` manuscript in the kms-latex standard (XeLaTeX + biber).
- `numerics/rust/` analytic-constant verification plus a P1 finite-element
  cross-check on `cartan-dec` box meshes: the assembled stiffness/mass
  generalised eigenproblem gives the sharp Poincare constant `1/sqrt(lambda_1)`
  (confirmed against the exact `2 pi^2`), and a manufactured-solution study
  confirms first-order `H^1` convergence. Run `cargo run --bin report` for the
  full verdict.
- `numerics/python/` SymPy cross-checks, managed by uv.

## Dependency chain

One-dimensional Poincaré inequality, then a per-coordinate-direction bound on a
box or convex domain via Fubini, then the averaged domain Poincaré inequality, a
density extension to $H_0^1$, the continuity and coercivity of $B$, and finally
Lax-Milgram to conclude existence and uniqueness. The one-dimensional step is
slated as a standalone Mathlib pull request.

## Build

```bash
# Lean
cd lean && lake build

# Paper
cd latex/manuscript && latexmk -xelatex main.tex

# Rust numerics
cd numerics/rust && cargo test

# Python checks
cd numerics/python && uv run python -m pytest
```

## Licensing

To be settled with the collaborators. Lean code intended for upstream Mathlib
is contributed under Apache-2.0 to match the Mathlib licence.

## Toolchain

Lean `v4.29.1` with Mathlib (fork-stable worktree); XeLaTeX with biber, TeX Live
2024 or later; Rust (stable) with the `cartan` stack; Python via uv.
