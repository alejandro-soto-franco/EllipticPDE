# EllipticPDE

A Lean 4 formalisation, on top of Mathlib, of the solvability theory of linear
second-order elliptic operators in divergence form on a bounded domain:

$$-\nabla\cdot(A\nabla u) + b\cdot\nabla u + c\,u = f \ \text{ in } \Omega,
\qquad u = 0 \ \text{ on } \partial\Omega,$$

with $A$ uniformly elliptic with bounded measurable coefficients. The weak
formulation seeks $u \in H_0^1(\Omega)$ satisfying $B[u,v] = \langle f, v\rangle$
for every $v \in H_0^1(\Omega)$, where $B$ is the associated bilinear form.

The drift term is permitted to be non-zero, so $B$ is in general non-symmetric
and the problem carries no variational structure. Existence runs through
Lax-Milgram.

## Results

Proved for the general operator `EllipticPdes.Sobolev.FullEllipticOp`, with no
`sorry` in the development:

- existence and uniqueness of the weak solution,
- the Gårding inequality,
- the complete Fredholm alternative: kernel, index, and solvability,
- the resolvent bound,
- spectral compactness of the operator, and
- interior $H^2$ regularity, as `EllipticPdes.Regularity.interior_H2_estimate`.

Higher $H^k$ regularity and Schauder $C^{k,\alpha}$ estimates are roadmap items.

## Dependency chain

The analytic content reduces to the one-dimensional Poincaré inequality. From
there: a per-coordinate-direction bound on a box or convex domain by Fubini, the
averaged domain Poincaré inequality, a density extension to $H_0^1$, continuity
and coercivity of $B$, and Lax-Milgram for existence and uniqueness. The Fredholm
alternative, the resolvent bound, and spectral compactness follow for the general
operator.

## Layout

- `lean/` the formalisation. A standalone lake project pinned to Lean
  `v4.31.0-rc1`.
- `numerics/rust/` analytic-constant verification and a P1 finite-element
  cross-check on box meshes. The assembled stiffness and mass generalised
  eigenproblem recovers the sharp Poincaré constant, and a manufactured-solution
  study confirms first-order $H^1$ convergence. Run `cargo run --bin report` for
  the full verdict.
- `numerics/python/` SymPy cross-checks, managed by uv.

## Build

```bash
cd lean && lake build

cd numerics/rust && cargo test

cd numerics/python && uv run python -m pytest
```

CI builds the formalisation and checks that it stays free of `sorry`.

## Toolchain

Lean `v4.31.0-rc1` with Mathlib. Rust, stable toolchain. Python via uv.

## Licence

Apache-2.0.
