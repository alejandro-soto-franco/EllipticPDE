# EllipticPDE

A Lean 4 formalisation of the solvability theory of linear
second-order elliptic operators in divergence form on a bounded domain:

$$-\nabla\cdot(A\nabla u) + b\cdot\nabla u + c u = f \ \text{ in } \Omega,
\qquad u = 0 \ \text{ on } \partial\Omega,$$

with $A$ uniformly elliptic with bounded measurable coefficients. The weak
formulation seeks $u \in H_0^1(\Omega)$ satisfying $B[u,v] = \langle f, v\rangle$
for every $v \in H_0^1(\Omega)$, where $B$ is the associated bilinear form.

The drift term is permitted to be non-zero, so $B$ is in general non-symmetric
and the problem has no variational structure. Existence runs through
Lax-Milgram.

**Symmetry of $a^{ij}$ is never assumed.** Evans §6.1.1 assumes $a^{ij} =
a^{ji}$ throughout, and Gilbarg-Trudinger ch. 8 assumes it for the principal
part. `EllipticPdes.Sobolev.EllipticCoeff` takes an arbitrary measurable
matrix: uniform ellipticity constrains the quadratic form $A(x)\xi\cdot\xi$
and the entries, and neither condition sees the antisymmetric part of $A(x)$.
Symmetry enters at one declaration and one only, the spectral theorem
`symmetric_fullElliptic_spectral`, whose argument `hAsymm` asks $a^{ij} =
a^{ji}$ a.e. on $\Omega$, and which needs it because the spectral theorem for
compact self-adjoint operators does. With $A$ non-symmetric the formal adjoint
$L^{*}$ has principal part built from $A^{\top}$, which is the transpose
problem the Fredholm results state.

## Results

Proved for the general operator `EllipticPdes.Sobolev.FullEllipticOp`, with no
`sorry` in the library:

- existence and uniqueness of the weak solution,
- the Gårding inequality,
- the complete Fredholm alternative: kernel, index, and solvability,
- the resolvent bound,
- spectral compactness of the operator,
- interior $H^2$ regularity, as `EllipticPdes.Regularity.interior_H2_estimate`,
- higher interior regularity at every order, as
  `EllipticPdes.Regularity.higher_interior_regularity`,
- infinite differentiability in the interior, as
  `EllipticPdes.Regularity.interior_smooth`, and
- interior Hölder continuity of the solution at exponent $\tfrac12$ in dimensions
  one, two and three, as `EllipticPdes.Embedding.interior_holder_estimate_one`,
  `interior_holder_estimate_two` and `interior_holder_estimate`, and
- interior Hölder continuity of finite order in every dimension, as
  `EllipticPdes.Regularity.exists_contDiffOn_holder_ball`: $m$ orders of weak
  derivative on $V$ give a $C^{k,1/2}$ representative on a ball whenever
  $k + 1 + \lfloor n/2 \rfloor \le m$. This is case (ii) of Guo's Sobolev
  embedding (Theorem IV.2.3) at $p = 2$,
- the same estimate for the weak solution itself, as
  `EllipticPdes.Regularity.interior_holder_of_weakSolution`, which discharges
  that supply of weak derivatives from the equation through
  `higher_interior_regularity` and is the $C^{k,1/2}$ interior estimate in
  every dimension and at every finite order,
- the Sobolev embedding of $H_0^1(\Omega)$, as
  `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01` at the critical exponent on any
  measurable domain and `eLpNorm_le_of_mem_H01_of_isBounded` at every exponent
  below it on a bounded one, bundled as the continuous linear map
  `EllipticPdes.Embedding.sobolevEmbL`, and
- integrability of the weak solution above $L^2$, as
  `EllipticPdes.Embedding.eLpNorm_weakSolution_le`: on a bounded domain in
  dimension greater than two the solution lies in $L^q(\Omega)$ up to the
  critical exponent, with $\|u\|_{L^q} \le K \|f\|_{L^2}$, and
- Rellich-Kondrachov below the critical exponent, as
  `EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt`: that embedding is
  compact at every $q < 2^{\star}$, on the interpolation inequality
  `EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow`,
- weak sequential compactness, as `EllipticPdes.Analysis.exists_weakLimit`: a
  bounded sequence in a real Hilbert space has a subsequence whose inner products
  converge against every vector, which is Evans §D.4 Theorem 3 read through Riesz
  representation and the compactness the direct method of the calculus of
  variations runs on,
- the direct method under a subcritical constraint, as
  `EllipticPdes.Embedding.exists_minimiser_of_lt`: on the unit ball the $H_0^1$
  norm attains its minimum on the functions of unit $L^q$ norm for
  $2 \le q < 2^{\star}$, the weak limit of a minimising sequence coming from
  `exists_weakLimit` and the constraint passing to that limit through
  `rellichEmbL_isCompact_of_lt`. At $2^{\star}$ the second step fails, which is
  the exponent restriction Guo writes as $p + 1 < 2^{\star}$ for
  $-\Delta u = u^p$,
- the Euler-Lagrange equation of that minimiser, as
  `EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt`: it is a weak
  solution of $-\Delta u + u = \lambda|u|^{q-2}u$ with
  $\lambda = \|u\|_{H_0^1}^2$, so the multiplier is named rather than merely
  asserted to exist. The constraint is differentiated by
  `EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow`, and the abstract form of
  the equation is `EllipticPdes.Analysis.euler_lagrange_of_norm_min`,
- the same equation with no lower-order term, as
  `EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt`: minimising the
  Dirichlet energy $\int|\nabla u|^2$ in place of the graph norm gives a weak
  solution of $-\Delta u = \lambda|u|^{q-2}u$ with
  $\lambda = \int|\nabla u|^2 > 0$, which is the equation of Guo IX.1 and of
  Evans §8.4.1 Theorem 2. The minimiser comes from the abstract direct method
  `EllipticPdes.Analysis.exists_bilin_minimiser` and the equation from
  `EllipticPdes.Analysis.euler_lagrange_of_bilin_min`,
- the variational principle for the principal eigenvalue, as
  `EllipticPdes.Sobolev.exists_principal_eigenpair`: for a symmetric coercive
  form with the Rellich compact embedding, the infimum
  $\lambda_1 = \inf\{B[u,u] : \|u\|_{L^2} = 1\}$ is attained and a minimiser
  solves $B[u,v] = \lambda_1 (u,v)$ for every $v$, with
  `principalEigenvalue_le_of_weak_eigen` placing $\lambda_1$ below every weak
  eigenvalue and `dirichlet_principal_eigenpair` the instance at $-\Delta$ on a
  bounded measurable domain. `dirichlet_principal_eigenpair_of_bounded` asks for
  boundedness alone, the Poincaré inequality naming the coercivity constant,
- the later eigenvalues by constrained minimisation, as
  `EllipticPdes.Sobolev.exists_higher_eigenpair`: minimising over the part of
  the unit $L^2$ sphere orthogonal to a finite orthonormal family of
  eigenfunctions produces another eigenpair, whose eigenvalue is at least
  $\lambda_1$. The multipliers of the extra constraints drop out, since
  $B[u, w_i] = \lambda_i \langle u, w_i \rangle_{L^2} = 0$ on the admissible
  complement, so the minimiser is a weak eigenfunction of the whole space,
- the eigenvalue sequence, as `EllipticPdes.Sobolev.exists_eigen_family`:
  iterating that step gives, for every $n$, an $L^2$-orthonormal family of $n$
  weak eigenfunctions with $\lambda_1 \le \cdots \le \lambda_n$, each named by
  a Rayleigh quotient over the vectors orthogonal to its predecessors. The
  recursion asks at each stage for a vector of nonzero $L^2$ class orthogonal to
  the family built so far, which on a bounded domain is the infinite
  dimensionality of $H_0^1(\Omega)$. `dirichlet_eigen_family_of_bounded` is the
  instance at $-\Delta$, reading $0 < \lambda_1 \le \cdots \le \lambda_n$, and
  `dirichlet_eigen_family_ball` discharges the last side condition on the unit
  ball: `orth_family_nonempty_ball` puts $n$ bumps at the points
  $((2k+1)/(2n) - 1/2)e_i$, whose supports are disjoint because the centres are
  $1/n$ apart and the radii are $1/(2n)$, so a combination of $m+1$ of them is
  orthogonal to any $m$ given vectors,
- the Dirichlet spectrum of the unit ball with no side hypothesis, as
  `EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball`: for $d > 2$ the
  Rayleigh infimum on $H_0^1(B_1)$ is attained, is positive, and its minimiser
  solves the weak eigenvalue problem. `exists_embL2_ne_zero_ball` discharges the
  nonemptiness the general statements assume, which a domain of measure zero
  fails,
- positivity and finite multiplicity of the Dirichlet eigenvalues, as
  `EllipticPdes.Sobolev.weak_eigenvalue_pos` and
  `EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace`: every weak
  eigenvalue of a symmetric coercive form is at least $\lambda_1 > 0$, and each
  eigenspace of the solution operator at a nonzero eigenvalue is finite
  dimensional, the operator being compact. On the unit ball
  `dirichlet_eigenvalue_pos_ball` asks for $d > 2$ and nothing else,
- the optimal constant in the Poincaré inequality, as
  `EllipticPdes.Sobolev.dirichlet_poincare_sharp` with the equality case
  `dirichlet_poincare_attained`: $\lambda_1 \|u\|_{L^2}^2 \le \int |\nabla u|^2$
  on all of $H_0^1(\Omega)$, and some $u$ of unit $L^2$ norm meets it,
- the local step of global approximation, as
  `EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub`: a
  mollification of a shift converges in $L^p$ to the function, as the shift and
  the radius go to zero together, which is what lets a mollifier near the
  boundary see only points where the function is defined. Convolution commutes
  with translation, so the mollification error of the shift is the shift of the
  mollification error and has the same norm,
- continuity of translation in $L^p$, as
  `EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub`: the $L^p$ distance
  between a function and its translate tends to zero with the translation, which
  is what bounds the shift into the domain of the global approximation theorem.
  Mathlib has the two halves, translation as an $L^p$ isometry
  and density of the continuous compactly supported functions, and not the
  statement,
- the two rigid motions the extension operator runs on, as
  `EllipticPdes.Extension.hasWeakGradOn_comp_translate` and
  `EllipticPdes.Extension.hasWeakGradOn_comp_reflect`: reflection in a
  coordinate hyperplane sends a weak gradient on a set to a weak gradient on the
  preimage, with the sign negative exactly in the reflected direction. The
  reflection is a linear isometry, so it preserves Lebesgue measure and every
  $L^p$ seminorm, and the statement asks nothing of the set, which is what lets
  a boundary chart reflect across the image of a hyperplane. Translation moves a
  weak gradient with no sign and no Jacobian, which is what the shift into the
  domain of the global approximation theorem needs,
- both cases of the order-$k$ embedding off `p = 2`. Case (ii) is
  `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general`: the ladder
  runs for $s$ rungs from $L^{p_0}$ and Morrey reads the Hölder exponent off the
  exponent it reaches, which `morreyExponent_eq_ladder` identifies as
  $s + 1 - d/p_0$, the $\lfloor n/p \rfloor + 1 - n/p$ of Evans §5.6.3
  Theorem 6 at $s = \lfloor d/p_0 \rfloor$. When $d/p_0$ is an integer the
  ladder reaches every finite exponent and the Hölder exponent is free in
  $(0,1)$, which is the other case that statement separates out,
- the Sobolev ladder off `p = 2`, as
  `EllipticPdes.Embedding.memLp_of_gradClosed_general`: the rung iterates from
  any base exponent $p_0 \in [1, \infty)$, and
  `memLp_of_gradClosed_general_ideal` lands on the exponent
  $1/q = 1/p_0 - s/d$ that Evans §5.6.3 Theorem 6 clause (i) names, under his
  strict rung condition $p_0 s < d$. Below $p_0 = 2$ a target can sit under the
  conjugate exponent $d/(d-1)$, where the rung from $p_0$ overshoots and the
  exponent is lowered onto the target by the finiteness of the ball's measure,
- the two general Sobolev estimates with their constants, as
  `EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep` and
  `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound`: one
  constant, quantified before the family, taking a uniform $L^2$ bound over the
  outer ball to the $L^q$ bound and to the Hölder seminorm on the inner one, and
- the Hölder exponent in even dimension, as
  `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even`: any
  $\gamma \in (0,1)$, which is the interval Evans §5.6.3 Theorem 6 leaves open
  when $n/p$ is an integer. In odd dimension the reciprocal the ladder lands on
  caps the exponent at $2d$ and forces $\gamma = 1/2$.

The embedding of $H_0^1(\Omega)$ runs the Gagliardo-Nirenberg-Sobolev
inequality on test functions and passes it to their closure. `poincare_H01`
makes that passage by continuity, its estimate being a closed condition on a
continuous function of the graph. The two sides of the Sobolev estimate sit at
different exponents, which leaves lower semicontinuity in place of continuity:
convergence in $H^1$ gives convergence of the function coordinates in
$L^2(\Omega)$, hence in measure, and Fatou's lemma along an almost-everywhere
convergent subsequence takes the bound to the limit. The transfer reads the
test-function estimate as a hypothesis at an arbitrary exponent, so each variant
of the inequality reaches $H_0^1(\Omega)$ by supplying it.

Compactness at those exponents refines the $L^2$ statement rather than repeating
its proof. Evans and Guo both mollify, bound the $L^1$ error uniformly over a
bounded family, interpolate, and finish with Arzelà-Ascoli. The first and last
moves give compactness at the lower exponent, which `embL2_isCompact` already
supplies from a translation modulus and without an extension operator. The
interpolation does the rest: a finite net of the unit ball's image in
$L^2(\Omega)$ is a net in $L^q(\Omega)$, at the radius the estimate names, once
the $L^{2^{\star}}$ seminorms of the differences are bounded on the ball. Below
$L^2$ no interpolation is needed, the embedding factoring through the $L^2$ one
along the inclusion a finite measure supplies.

That range is optimal, as
`EllipticPdes.Embedding.not_isCompactOperator_critEmb`: at $2^{\star}$ itself
the embedding is bounded and not compact. Dilating by $\lambda$ scales the
$L^p$ seminorm by $\lambda^{d/p}$ and each derivative by $\lambda^{-1}$
(`EllipticPdes.Analysis.eLpNorm_comp_smul` and
`EllipticPdes.Embedding.eLpNorm_partialD_dilate`), so the renormalised dilates
$\lambda^{1-d/2}\varphi(\cdot/\lambda)$ of a bump keep their $L^{2^{\star}}$
norm and their gradient norm while losing their $L^2$ norm, and their images
have no convergent subsequence.

The Hölder estimate chains the $H^2$ estimate through Morrey's inequality on a
ball. Supporting layers supply Morrey's inequality itself, the
Gagliardo-Nirenberg-Sobolev bootstrap `exists_eLpNorm_sobolevConj_le` in general
dimension and at a general exponent pair, Campanato's characterisation of Hölder
continuity with its converse, and the Caccioppoli inequality.

Out of $L^2$ data one Sobolev step reaches Morrey only below dimension four:
$1/p' = 1/p - 1/d$ gives $p' > d$ only for $p > d/2$, and the window
$d/2 < p \le 2$ is empty once $d \ge 4$. Iterating the step reaches every
dimension, at one weak derivative per rung, and the iteration runs on a family
closed under weak differentiation: an index type, a function per index, and a
successor naming the weak derivatives of that function, so one induction climbs
with no separate induction on the order of differentiation.

Two ladders are built on that family. `memLp_of_gradClosed` climbs at the half
step $1/(2d)$ and reaches $L^{2d}$ after $d - 1$ rungs, keeping every
intermediate reciprocal positive; it is run where weak derivatives of every
order are available, and its consumer is `interior_smooth`.
`memLp_of_gradClosed_fullStep` climbs at the full step $1/d$ and reaches the
same exponent after $\lfloor d/2 \rfloor$ rungs, bounding the supply with a
depth function; its consumer is `exists_contDiffOn_holder_ball`, where the
supply is finite. The full step lands on the reciprocal $0$ when $d$ is even,
and the rung form `exists_eLpNorm_sobolevConj_le_of_le`, which takes its
hypothesis in $L^q$ for any $q \ge p$ while concluding at the conjugate of $p$,
is what covers that case. Smoothness in the interior is the half-step ladder
followed by
`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`, which turns a
continuous weak gradient back into a classical derivative.

Differentiating the `L^q` constraint is the one analytic step the direct method
needs beyond compactness. The integrand's derivative in `t` is bounded on
$|t| < 1$ by $q(|u| + |v|)^{q-1}|v|$, whose first factor sits in $L^{q/(q-1)}$
and whose second sits in $L^q$, so Hölder's inequality supplies a dominating
function and mathlib's `hasDerivAt_abs_rpow` supplies the pointwise derivative,
including at the origin. Fermat's theorem then applies to
$t \mapsto \|U + tV\|^2 - \lambda\|T(U + tV)\|_{L^q}^2$, which vanishes at
$t = 0$ and is nonnegative everywhere, since rescaling $U + tV$ back to the
constraint set is admissible wherever its image is nonzero. Homogeneity of the
`L^q` norm is what makes that rescaling available and replaces the implicit
function theorem Evans applies to a general constraint. The same argument runs
at any symmetric positive semidefinite form in place of the squared norm, since
it uses only the quadratic expansion of $Q(U + tV)$ and the degree-two
homogeneity of $Q$: `EllipticPdes.Analysis.euler_lagrange_of_quadratic_min` is
that statement, and at the Dirichlet form it gives Guo's equation with no
lower-order term.

The eigenvalue chapter has two independent routes to the Dirichlet spectrum.
`solOp_spectral` runs the spectral theorem for the compact self-adjoint solution
operator and produces the whole orthonormal basis of eigenfunctions with no
formula for any eigenvalue. The variational route names the first one: the same
direct method as `exists_minimiser_of_lt`, at a quadratic constraint, where weak
lower semicontinuity of the form is the expansion of
$0 \le B[u_k - w, u_k - w]$ against $B[u_k, w] \to B[w, w]$, and the
Euler-Lagrange step is one variable, the map
$t \mapsto B[u + tv, u + tv] - \lambda_1\|u + tv\|_{L^2}^2$ being a quadratic
that vanishes at $t = 0$ and is nonnegative everywhere. Repeating the step
against the eigenfunctions already found names every later eigenvalue the same
way. `exists_bilin_minimiser` states the direct method once, for a symmetric
coercive form and any compact constraint map into a normed space, and both the
Rayleigh problem and the semilinear problem are instances of it. Positivity of
the minimiser and simplicity of $\lambda_1$, the remaining clauses of Evans
§6.5.1 Theorem 2, need the maximum principle and are open.

Boundary $H^2$ regularity has its foundations in place and its headline estimate
open: the half-ball geometry, tangential difference quotients with their $H_0^1$
admissibility, and the weak quotient rule dividing a $C^1$ weight out of a weak
derivative. The boundary estimate itself is not reached, and Schauder
$C^{k,\alpha}$ estimates remain a roadmap item.

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
- `lean/AxiomAudit.lean` pins the axiom set of each headline result with
  `#print axioms` under `#guard_msgs`, built as a target of its own.
- `lean/Challenge.lean` and `lean/Solution.lean` are the Palomar submission pair
  for the six solvability results of Evans §6.2, with `lean/comparator.json` and
  `lean/formalization.yaml`.

## Build

```bash
cd lean && lake build      # includes the axiom pins in AxiomAudit.lean
cd lean && lake lint       # environment-level linter
cd lean && lake build Challenge Solution   # the Palomar pair
```

CI runs these on every push. It builds from a clean clone, asserts the
library is free of `sorry`, and pins every headline result to the axioms
`propext`, `Classical.choice` and `Quot.sound` through `AxiomAudit.lean`, where
each is pinned with `#guard_msgs`.

## Palomar

`lean/Challenge.lean` states six results of Evans §6.2 in Mathlib vocabulary alone:
the Gårding inequality, existence and uniqueness for a nonnegative zeroth-order
coefficient, the Fredholm alternative, solvability against the transpose problem,
the discrete set of exceptional shifts, and boundedness of the inverse. It inlines
the graph encoding of $H_0^1(\Omega)$, reads the bilinear form off the graph
coordinates as a sum of integrals, and leaves each statement `sorry`. Every result
but the Gårding inequality is stated for a bounded open $\Omega$, so the
Rellich-Kondrachov compact embedding is discharged rather than assumed. Openness is
what gives those five conclusions content: a test function has
$\operatorname{tsupport} \varphi \subseteq \Omega$, so on a set of positive measure
with empty interior every test function vanishes and $H_0^1(\Omega)$ is zero.
`lean/Solution.lean` states the same six statements under the same names and proves
them from the library.

Comparator looks a theorem up by name in both modules, so `Solution.lean` restates
the definitions instead of importing `Challenge.lean`. The two copies are kept
identical character for character by `verify/palomar_sync.py`, which CI runs:
drift there produces two statements that both elaborate and differ, which the
build would not catch.

The six `sorry`s in `Challenge.lean` are the placeholders Comparator requires.
Nothing under `EllipticPdes/` has one, and `Solution.lean` has none either:
each of its six results pins its own axiom set with `#guard_msgs`, so a `sorryAx`
reaching any of them fails the build.

## Toolchain

Lean `v4.31.0-rc1` with Mathlib.

## Licence

Apache-2.0.
