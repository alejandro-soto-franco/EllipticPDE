# EllipticPDE

A Lean 4 formalisation of the solvability theory of linear
second-order elliptic operators in divergence form on a bounded domain:

$$-\nabla\cdot(A\nabla u) + b\cdot\nabla u + c u = f \ \text{ in } \Omega,
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
- spectral compactness of the operator,
- interior $H^2$ regularity, as `EllipticPdes.Regularity.interior_H2_estimate`, and
- interior Hölder continuity of the solution at exponent $\tfrac12$ in dimensions
  one, two and three, as `EllipticPdes.Embedding.interior_holder_estimate_one`,
  `interior_holder_estimate_two` and `interior_holder_estimate`.

The Hölder estimate chains the $H^2$ estimate through Morrey's inequality on a
ball. Supporting layers carry Morrey's inequality itself, the
Gagliardo-Nirenberg-Sobolev bootstrap `exists_eLpNorm_sobolevConj_le` in general
dimension and at a general exponent pair, Campanato's characterisation of Hölder
continuity with its converse, and the Caccioppoli inequality.

Dimension four and above stays open. Morrey needs a gradient in $L^{p'}$ with
$p' > d$, the interior $H^2$ estimate supplies $L^2$ second derivatives, and
$1/p' = 1/p - 1/d$ gives $p' > d$ only for $p > d/2$, so the exponent window
$d/2 < p \le 2$ is empty once $d \ge 4$. One Sobolev step never reaches Morrey
there; those dimensions need iteration through the $H^k$ ladder.

Two further chains have their foundations in place and their headline estimates
open. Higher interior regularity has the admissibility step,
`EllipticPdes.Regularity.interior_cutoffGrad_mem_H01`, returning the cutoff of a
first derivative to $H_0^1(\Omega)$, and the differentiated-equation identity
`differentiated_weakForm_of_weakSolution`, which carries every hypothesis
discharged from the weak formulation apart from a weak derivative of the datum.
Boundary $H^2$ regularity has the half-ball geometry, tangential difference
quotients with their $H_0^1$ admissibility, and the weak quotient rule dividing a
$C^1$ weight out of a weak derivative. The interior $H^3$ and boundary $H^2$
estimates themselves are not reached, and Schauder $C^{k,\alpha}$ estimates remain
a roadmap item.

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
- `lean/Gates.lean` axiom gates for the headline results, built as a target of
  its own.

## Build

```bash
cd lean && lake build      # includes the axiom gates in Gates.lean
cd lean && lake lint       # environment-level linter
```

CI runs both on every push. It builds from a clean clone, asserts the
development is free of `sorry`, and holds every headline result to the axioms
`propext`, `Classical.choice` and `Quot.sound` through `Gates.lean`, where each
is pinned with `#guard_msgs`.

## Toolchain

Lean `v4.31.0-rc1` with Mathlib.

## Licence

Apache-2.0.
