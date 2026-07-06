# elliptic-pdes

A Lean 4 formalisation, on top of Mathlib, of the solvability theory of linear
second-order elliptic operators in divergence form, on a bounded domain:

$$-\operatorname{div}(A\nabla u) + b\cdot\nabla u + c\,u = f \ \text{ in } \Omega, \qquad u = 0 \ \text{ on } \partial\Omega,$$

with $A$ uniformly elliptic with bounded measurable coefficients. The weak
formulation seeks $u\in H_0^1(\Omega)$ with $B[u,v]=\langle f,v\rangle$ for all
$v\in H_0^1(\Omega)$, where $B$ is the associated bilinear form.

The development machine-verifies, `sorry`-free, for the general operator
`EllipticDirichlet.Sobolev.FullEllipticOp`:

- existence and uniqueness of the weak solution,
- the Gårding inequality,
- the complete Fredholm alternative (kernel, index, and solvability),
- the resolvent bound, and
- spectral compactness of the operator.

The analytic content reduces to the one-dimensional Poincaré inequality,
lifted to a box by Fubini's theorem and averaging.

Regularity of the weak solution (interior $H^2$, higher $H^k$, and Schauder
$C^{k,\alpha}$ estimates) is a roadmap item, not yet formalised.

Authors: Alejandro José Soto Franco and Kobe Marshall-Stevens.

## Methodology

The accompanying paper presents the development through a warrant-explicit
realisation of Lean in prose: every step of every proof carries an
obligation, discharged by a named Lean declaration, warranted by a
provenance-tracked citation, or routine. A formal proof has no remaining
obligations. This methodology is a contribution in its own right, independent
of the elliptic theory it demonstrates.

## Three tracks

| Track | Tool | Contents |
|-------|------|----------|
| Formal | Lean 4 + Mathlib | `lean/` typed statements and proofs |
| Theory | LaTeX (kms-latex) + SymPy | `latex/` manuscript and literature review, `numerics/python/` symbolic checks |
| Numerics | Rust (cartan stack) | `numerics/rust/` FEM cross-check and constant verification |

## Layout

- `lean/` standalone lake project pinned to Lean `v4.31.0-rc1`, depending on
  Mathlib through the shared `mathlib4-fork-stable` worktree. Build artefacts
  live under `/home/lean-caches/elliptic-dirichlet` via the `.lake` symlink.
- `latex/manuscript/` the paper (XeLaTeX + biber, kms-latex standard).
- `latex/litreview/` a companion literature review, tracking each result
  against its classical source, its Mathlib status, and its formalisation
  status here.
- `numerics/rust/` analytic-constant verification plus a P1 finite-element
  cross-check on `cartan-dec` box meshes: the assembled stiffness/mass
  generalised eigenproblem gives the sharp Poincaré constant
  `1/sqrt(lambda_1)` (confirmed against the exact `2 pi^2`), and a
  manufactured-solution study confirms first-order `H^1` convergence. Run
  `cargo run --bin report` for the full verdict.
- `numerics/python/` SymPy cross-checks and manuscript figures, managed by uv.
- `verify/` the formal-CI gates: equation-coverage linting, prose linting,
  and Lean source linting.

## Formal CI

`adduce formalize check` gates the hand-written statements in the manuscript
(the `\adducethm`/`\adduceuses` macros) against the Lean declarations they
cite, so a statement cannot drift from its proof without failing CI.

## Dependency chain

One-dimensional Poincaré inequality, then a per-coordinate-direction bound
on a box or convex domain via Fubini, then the averaged domain Poincaré
inequality, a density extension to $H_0^1$, the continuity and coercivity of
$B$, and Lax-Milgram to conclude existence and uniqueness. From there, the
Fredholm alternative, the resolvent bound, and spectral compactness follow
for the general operator. The one-dimensional step is slated as a standalone
Mathlib pull request.

## Build

```bash
# Lean
cd lean && lake build

# Paper
cd latex/manuscript && latexmk -xelatex main.tex

# Literature review
cd latex/litreview && latexmk -xelatex main.tex

# Rust numerics
cd numerics/rust && cargo test

# Python checks
cd numerics/python && uv run python -m pytest
```

## Licensing

To be settled with the collaborators. Lean code intended for upstream Mathlib
is contributed under Apache-2.0 to match the Mathlib licence.

## Toolchain

Lean `v4.31.0-rc1` with Mathlib (fork-stable worktree); XeLaTeX with biber,
TeX Live 2024 or later; Rust (stable) with the `cartan` stack; Python via uv.
