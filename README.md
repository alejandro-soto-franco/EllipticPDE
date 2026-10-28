# EllipticPDE

[![Palomar: PALOMAR-2026-10-15-000012](https://img.shields.io/badge/Palomar-PALOMAR--2026--10--15--000012-2b7a78.svg)](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000012&version=1)

A Lean 4 formalisation of the solvability theory of linear
second-order elliptic operators in divergence form on a bounded domain:

$$-\nabla\cdot(A\nabla u) + b\cdot\nabla u + c u = f \ \text{ in } \Omega,
\qquad u = 0 \ \text{ on } \partial\Omega,$$

with $A$ uniformly elliptic with bounded measurable coefficients. The weak
formulation seeks $u \in H_0^1(\Omega)$ satisfying $B[u,v] = \langle f, v\rangle$
for every $v \in H_0^1(\Omega)$, where $B$ is the associated bilinear form.

Because the drift term may be non-zero, $B$ is in general non-symmetric and the problem
has no variational structure. Existence runs through Lax-Milgram in the form
`IsCoercive.existsUnique_apply_eq` built on Mathlib's
`IsCoercive.continuousLinearEquivOfBilin`.

The Hilbert-space theory is stated over a finite-dimensional real inner product space
$E$ with no coordinates: the graph space `H1Graph μ Ω` of pairs $(u, \nabla u)$ in
$L^2(\Omega) \times L^2(\Omega; E)$, the coefficient field $a : E \to (E \to_L E)$, the
weak derivative `HasWeakFDerivOn` built on Mathlib's distributions, and the abstract
layers `GardingForm` and `Variational` over any Hilbert space, of which the elliptic
operators are instances. The coordinate statements on `EuclideanSpace ℝ (Fin d)` are the
instances at $E = \mathbb{R}^d$. The regularity theory, the Sobolev embeddings and the
extension operator use coordinate directions and are stated there.

**Solvability assumes no symmetry of $a^{ij}$.** Evans §6.1.1 assumes $a^{ij} = a^{ji}$
throughout and Gilbarg-Trudinger ch. 8 assumes it for the principal part.
`EllipticPdes.Sobolev.EllipticCoeff` takes an arbitrary measurable matrix: uniform
ellipticity constrains the quadratic form $A(x)\xi\cdot\xi$ and the entries without
seeing the antisymmetric part of $A(x)$. Nothing in the Gårding inequality, the
existence theorems, the Fredholm alternative, the exceptional set or the resolvent bound
asks about that part. Symmetry is a hypothesis only at the results further up whose
proofs need it: the spectral theorems `Sobolev.symmetric_fullElliptic_spectral` and
`Sobolev.symmetric_fullElliptic_spectral_of_bounded` take `hAsymm : a^{ij} = a^{ji}`
a.e. on $\Omega$ because the spectral theorem for compact self-adjoint operators does;
the variational eigenvalue layer above them asks the same of the bilinear form in
`hsymm : B U V = B V U`; and the classical maximum principles ask
$a^{ij}(x) = a^{ji}(x)$ pointwise because they read the non-divergence operator through
a symmetric second-derivative matrix. With $A$ non-symmetric the transpose problem the
Fredholm results state has the formal adjoint $L^{*}$, whose principal part is built
from $A^{\top}$.

## General theory

Over a finite-dimensional real inner product space `E` (normed space for the Campanato
and mollifier results) with the volume measure where the statement needs one and any
measure otherwise. Declarations are named without their `EllipticPdes.` prefix.

| Result | Declaration |
|---|---|
| A continuous weak derivative is the Fréchet derivative | `HasWeakFDerivOn.hasFDerivAt` |
| Weak derivative, uniqueness and bridges to the coordinate predicates | `HasWeakFDerivOn`, `HasWeakFDerivOn.ae_eq`, `Sobolev/WeakDeriv.lean` |
| Graph space, `W^{1,2}` and `H_0^1` | `H1Graph`, `H1Graph.W12`, `H1Graph.H01` |
| Poincaré inequality on a slab and on a bounded set | `Poincare.integral_sq_le_of_tsupport_subset_slab`, `H1Graph.poincare_H01_of_bounded` |
| Rellich-Kondrachov on a bounded set | `H1Graph.embL2_isCompact` |
| Gårding inequality | `DivForm.FullEllipticOp.garding` |
| Existence and uniqueness after a shift, and for a nonnegative zeroth-order term | `DivForm.FullEllipticOp.weak_solution`, `DivForm.FullEllipticOp.weak_solution_of_nonneg_zeroth_of_bounded` |
| Fredholm alternative and transpose solvability | `DivForm.FullEllipticOp.fredholm_alternative_of_bounded`, `DivForm.FullEllipticOp.solvable_iff_orthogonal_transpose_of_bounded` |
| Exceptional set and resolvent bound | `DivForm.FullEllipticOp.existence_three_of_bounded`, `DivForm.FullEllipticOp.resolvent_bound_of_bounded` |
| Spectral theorem for a symmetric operator | `DivForm.FullEllipticOp.symmetric_spectral_of_bounded` |
| Abstract Fredholm and spectral layers on a Hilbert space | `GardingForm`, `Variational` |
| The same bounded-domain theorems for any additive Haar measure | `DivForm.FullEllipticOp.fredholm_alternative_of_bounded_haar` and the other `_of_bounded_haar` theorems |
| Interior smoothness of weak solutions | `DivForm.FullEllipticOp.interior_smooth`, `DivForm.FullEllipticOp.exists_weakSolution_interior_smooth` |
| `H⁻¹` as `f₀ - div F` with the minimal norm | `H1Graph.hneg_characterization` |
| Difference quotients along a vector | `Regularity.diffQuotAlong` |
| Hopf lemma, weak maximum and comparison principles | `Classical.hopf_lemma`, `Classical.nondivOperator.weak_maximum_principle`, `Classical.nondivOperator.comparison_principle` |
| Campanato's characterisation of Hölder continuity | `Campanato.Haar.campanato_holderOnWith` |
| Morrey, Gagliardo-Nirenberg, Young, chain rule | `Embedding/Morrey.lean`, `Embedding/WeakSobolev.lean`, `Analysis/Mollifier.lean`, `Embedding/WeakDerivChain.lean` |

Each is checked against the three classical axioms in `lean/AxiomAudit.lean`.

## Results

The first three rows are the Sobolev spaces on an open subset of `EuclideanSpace ℝ (Fin d)`.
The remaining rows are coordinate statements on that space for the operator
`EllipticPdes.Sobolev.FullEllipticOp`. The library has no `sorry`. Declarations are
named without their `EllipticPdes.` prefix.

| Result | Declaration |
|---|---|
| Weak derivative of every order with its uniqueness and linearity | `Sobolev.HasWeakDeriv`, `Sobolev.HasWeakDeriv.ae_eq` |
| $W^{k,p}(U)$ for $1 \le p \le \infty$ and its completeness | `Sobolev.Wkp`, `Sobolev.Wkp.completeSpace` |
| $H^k(U)$ and $W_0^{k,p}(U)$ | `Sobolev.Hk`, `Sobolev.W0kp`, `Sobolev.W0kp_le_Wkp` |
| Existence and uniqueness of the weak solution | `Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded` |
| Gårding inequality | `Sobolev.FullEllipticOp.garding` |
| Fredholm alternative: a nontrivial kernel or unique solvability for every datum | `Sobolev.FullEllipticOp.fredholm_alternative` |
| Finite-dimensional kernel | `Sobolev.FullEllipticOp.finiteDimensional_solSpace` |
| Kernel and adjoint kernel of equal dimension | `Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace` |
| Solvability exactly when the datum annihilates the adjoint kernel | `Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar` |
| Resolvent bound | `Sobolev.FullEllipticOp.resolvent_bound` |
| Spectral compactness | `Sobolev.spectrum_compact_operator` |
| Interior $H^2$ regularity | `Regularity.interior_H2_estimate` |
| Higher interior regularity at every order | `Regularity.higher_interior_regularity` |
| Infinite differentiability in the interior | `Regularity.interior_smooth` |
| The pointwise equation of the smooth representative | `Regularity.weakSolution_ae_eq_of_contDiffOn` |
| Classical solvability in the interior | `Regularity.exists_weakSolution_interior_classical` |
| Interior Hölder continuity at exponent $\tfrac12$ in dimensions one to three | `Embedding.interior_holder_estimate_one` |
| Interior Hölder continuity of finite order in every dimension | `Regularity.exists_contDiffOn_holder_ball` |
| The same estimate for the weak solution | `Regularity.interior_holder_of_weakSolution` |
| Sobolev embedding of $H_0^1(\Omega)$ | `Embedding.eLpNorm_le_of_mem_H01` |
| Integrability of the weak solution above $L^2$ | `Embedding.eLpNorm_weakSolution_le` |
| Rellich-Kondrachov below the critical exponent | `Embedding.rellichEmbL_isCompact_of_lt` |
| Weak sequential compactness | `Analysis.exists_weakLimit` |
| Direct method under a subcritical constraint | `Embedding.exists_minimiser_of_lt` |
| Euler-Lagrange equation of that minimiser | `Embedding.exists_weakSolution_semilinear_of_lt` |
| The same equation with no lower-order term | `Embedding.exists_weakSolution_dirichlet_of_lt` |
| Variational principle for the principal eigenvalue | `Sobolev.exists_principal_eigenpair` |
| Later eigenvalues by constrained minimisation | `Sobolev.exists_higher_eigenpair` |
| The eigenvalue sequence | `Sobolev.exists_eigen_family` |
| Dirichlet spectrum of the unit ball | `Sobolev.dirichlet_principal_eigenpair_ball` |
| Positivity and finite multiplicity of the Dirichlet eigenvalues | `Sobolev.weak_eigenvalue_pos` |
| Optimal constant in the Poincaré inequality | `Sobolev.dirichlet_poincare_sharp` |
| Local step of global approximation | `Extension.tendsto_eLpNorm_translate_convolution_sub` |
| Continuity of translation in $L^p$ | `Analysis.tendsto_eLpNorm_translate_sub` |
| The two rigid motions of the extension operator | `Extension.hasWeakGradOn_comp_translate` |
| The shear the extension operator runs on | `Extension.hasWeakGradOn_comp_shear` |
| Local half of the extension operator | `Extension.hasWeakGradOn_chartExt` |
| The $C^1$ boundary hypothesis | `Extension.HasC1Boundary` |
| The unit ball as an instance of it | `Extension.hasC1Boundary_ball` |
| Relabelling and reorientation | `Extension.hasWeakGradOn_comp_linearIsometry` |
| First step of the patching | `Extension.hasWeakGradOn_mul_cutoff_inter` |
| The finite chart cover | `Extension.exists_finite_chart_cover` |
| Partition of unity over that cover | `Extension.nonempty_boundaryPartition` |
| The local extension | `Extension.exists_localExtension` |
| The glued extension | `Extension.exists_extension` |
| The support clause | `Extension.exists_extension_subset` |
| The norm bound of clause (iii) | `Extension.exists_extension_subset_bound` |
| The operator as a linear map | `Extension.extLinear` |
| The operator between the Sobolev spaces | `Extension.exists_extW12` |
| Global approximation by functions smooth up to the boundary | `Extension.exists_smooth_tendsto_of_hasWeakGradOn` |
| Density of the smooth functions in $H^1(\Omega)$ | `Extension.exists_smooth_tendsto_of_mem_W12` |
| Rellich-Kondrachov on $H^1(\Omega)$ | `Sobolev.embW12_isCompact` |
| Poincaré's inequality with the mean subtracted | `Sobolev.poincare_wirtinger` |
| Poincaré's inequality on a ball | `Sobolev.poincare_ball` |
| Chain rule for weak gradients | `Embedding.hasWeakGradOn_comp` |
| Weak gradient of the positive part | `Embedding.hasWeakGradOn_posPart` |
| Weak gradients of the negative part and the absolute value | `Embedding.hasWeakGradOn_abs` |
| The weak gradient vanishes on level sets | `Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn` |
| The weak maximum principle | `Sobolev.weak_maximum_principle` |
| Compactly supported classes lie in $H^1_0$ | `Sobolev.mem_H01_of_hasCompactSupport` |
| Truncation in $H^1_0$ | `Sobolev.exists_mem_H01_posPart_sub_const` |
| The weak maximum principle in $H^1_0$ | `Sobolev.weak_maximum_principle_H01` |
| Uniqueness of the generalised Dirichlet problem | `Sobolev.eq_zero_of_weakSolution_H01` |
| The weak maximum principle with a transport term | `Sobolev.weak_maximum_principle_transport` |
| The classical weak maximum principle | `Classical.weak_maximum_principle` |
| The classical weak minimum principle | `Classical.weak_minimum_principle` |
| The classical weak maximum principle with $c \ge 0$ | `Classical.weak_maximum_principle_of_nonneg` |
| The classical weak minimum principle with $c \ge 0$ | `Classical.weak_minimum_principle_of_nonneg` |
| The strict maximum principle | `Classical.not_isLocalMax_of_nondivOp_neg` |
| The comparison principle | `Classical.comparison_principle` |
| Bound of a solution by its boundary values | `Classical.abs_le_of_nondivOp_eq_zero` |
| Hopf's lemma | `Classical.hopf_lemma` |
| The strong maximum principle | `Classical.strong_maximum_principle` |
| The strong maximum principle with $c \ge 0$ | `Classical.strong_maximum_principle_of_nonneg` |
| Uniqueness for the classical Dirichlet problem | `Classical.dirichlet_unique` |
| Hopf's lemma at a zero boundary value | `Classical.hopf_lemma_of_zero` |
| The strong maximum principle at a zero maximum | `Classical.strong_maximum_principle_of_zero` |
| The avoidance principle | `Classical.avoidance_principle` |
| Tangency at a boundary point forces equality | `Classical.eq_of_eq_of_fderiv_eq` |
| Uniqueness for the classical Neumann problem | `Classical.neumann_unique` |
| A priori bound from the maximum principle | `Classical.apriori_bound_abs` |
| The strong maximum principle for subharmonic functions | `Classical.strong_maximum_principle_subharmonic` |
| Difference quotients and weak derivatives | `Regularity.weakDeriv_of_diffQuot_bounded` |
| Additivity of a weak gradient | `Embedding.HasWeakGradOn.add_of_locallyIntegrableOn` |
| Completeness of $W^{1,2}$ | `Sobolev.instCompleteSpaceW12` |
| Completeness of $H^1_0$ | `Sobolev.instCompleteSpaceH01` |
| Existence for the shifted problem $Lu + \mu u = f$ | `Sobolev.FullEllipticOp.weak_solution` |
| Rellich compactness of $H^1_0$ into $L^2$ | `Sobolev.embL2_isCompact` |
| The Fredholm alternative for a compact operator | `Sobolev.fredholm_alternative_compact` |
| Morrey's inequality on a ball | `Embedding.morrey_ball` |
| Gagliardo-Nirenberg-Sobolev on a bounded $C^1$ domain | `Embedding.exists_eLpNorm_sobolevConj_le_domain` |
| Sobolev ladder on that domain | `Embedding.exists_const_memLp_of_gradClosed_domain` |
| Hölder continuity up to the boundary | `Embedding.exists_const_holderOnWith_of_gradClosed_domain` |
| Clause (ii) with classical derivatives | `Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain` |
| Both clauses of the order-$k$ embedding on a bounded $C^1$ domain | `Embedding.exists_const_memLp_of_gradClosed_domain_ideal` |
| Both cases of the order-$k$ embedding off $p = 2$ | `Embedding.exists_holderOnWith_of_gradClosed_general` |
| Sobolev ladder off $p = 2$ | `Embedding.memLp_of_gradClosed_general` |
| The two general Sobolev estimates with their constants | `Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep` |
| Hölder exponent in even dimension | `Embedding.exists_holderOnWith_of_gradClosed_even` |

<details>
<summary>Each result with its reading against the cited statement</summary>

- Existence and uniqueness of the weak solution.
- The Gårding inequality.
- The complete Fredholm alternative: kernel, index and solvability.
- The resolvent bound.
- Spectral compactness of the operator.
- Interior $H^2$ regularity as `EllipticPdes.Regularity.interior_H2_estimate`.
- Higher interior regularity at every order as
  `EllipticPdes.Regularity.higher_interior_regularity`.
- Infinite differentiability in the interior as
  `EllipticPdes.Regularity.interior_smooth`.
- Interior Hölder continuity of the solution at exponent $\tfrac12$ in dimensions one,
  two and three as `EllipticPdes.Embedding.interior_holder_estimate_one`,
  `interior_holder_estimate_two` and `interior_holder_estimate`.
- Interior Hölder continuity of finite order in every dimension as
  `EllipticPdes.Regularity.exists_contDiffOn_holder_ball`: $m$ orders of weak derivative
  on $V$ give a $C^{k,1/2}$ representative on a ball whenever
  $k + 1 + \lfloor n/2 \rfloor \le m$. This is case (ii) of the order-$k$ Sobolev
  embedding at $p = 2$.
- The pointwise equation of the smooth representative as
  `EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn`: a weak solution whose
  function coordinate has a $C^2$ representative on an open subset of the domain
  satisfies
  $-\sum_{i,j}\partial_j(a^{ij}\partial_i u) + \sum_i b^i \partial_i u + c u = f$ almost
  everywhere there when the diffusion is $C^1$. The classical gradient of the
  representative is a weak gradient on the open set and by uniqueness the weak gradient
  of the solution there. Integrating the weak formulation by parts once more against a
  function supported in the set leaves a residual that the fundamental lemma of the
  calculus of variations makes vanish.
  `exists_weakSolution_interior_classical` composes it with
  `exists_weakSolution_interior_smooth` and closes classical solvability in the interior
  on both halves of regularity and equation.
- The same estimate for the weak solution itself as
  `EllipticPdes.Regularity.interior_holder_of_weakSolution`, which discharges that
  supply of weak derivatives from the equation through `higher_interior_regularity` and
  is the $C^{k,1/2}$ interior estimate in every dimension and at every finite order.
- The Sobolev embedding of $H_0^1(\Omega)$ as
  `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01` at the critical exponent on any
  measurable domain and `eLpNorm_le_of_mem_H01_of_isBounded` at every exponent below it
  on a bounded one. The continuous linear map `EllipticPdes.Embedding.sobolevEmbL`
  bundles it.
- Integrability of the weak solution above $L^2$ as
  `EllipticPdes.Embedding.eLpNorm_weakSolution_le`: on a bounded domain in dimension
  greater than two the solution lies in $L^q(\Omega)$ up to the critical exponent with
  $\|u\|_{L^q} \le K \|f\|_{L^2}$.
- Rellich-Kondrachov below the critical exponent as
  `EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt`: that embedding is compact at
  every $q < 2^{\star}$ through the interpolation inequality
  `EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow`.
- Weak sequential compactness as `EllipticPdes.Analysis.exists_weakLimit`: a bounded
  sequence in a real Hilbert space has a subsequence whose inner products converge
  against every vector. This statement of Evans §D.4 Theorem 3 through Riesz
  representation supplies the compactness the direct method of the calculus of
  variations needs.
- The direct method under a subcritical constraint as
  `EllipticPdes.Embedding.exists_minimiser_of_lt`: on the unit ball the $H_0^1$ norm
  attains its minimum on the functions of unit $L^q$ norm for $2 \le q < 2^{\star}$. The
  weak limit of a minimising sequence comes from `exists_weakLimit` and the constraint
  passes to that limit through `rellichEmbL_isCompact_of_lt`. Failure of the second step
  at $2^{\star}$ is the subcritical restriction $p + 1 < 2^{\star}$ for
  $-\Delta u = u^p$.
- The Euler-Lagrange equation of that minimiser as
  `EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt`: the minimiser is a weak
  solution of $-\Delta u + u = \lambda|u|^{q-2}u$ with the multiplier named as
  $\lambda = \|u\|_{H_0^1}^2$. `EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow`
  differentiates the constraint and `EllipticPdes.Analysis.euler_lagrange_of_norm_min`
  states the abstract form of the equation.
- The same equation with no lower-order term as
  `EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt`: minimising the Dirichlet
  energy $\int|\nabla u|^2$ in place of the graph norm gives a weak solution of the
  equation $-\Delta u = \lambda|u|^{q-2}u$ of Evans §8.4.1 Theorem 2 with
  $\lambda = \int|\nabla u|^2 > 0$. The minimiser comes from the abstract direct method
  `EllipticPdes.Analysis.exists_bilin_minimiser` and the equation from
  `EllipticPdes.Analysis.euler_lagrange_of_bilin_min`.
- The variational principle for the principal eigenvalue as
  `EllipticPdes.Sobolev.exists_principal_eigenpair`: for a symmetric coercive form with
  the Rellich compact embedding, the infimum
  $\lambda_1 = \inf\{B[u,u] : \|u\|_{L^2} = 1\}$ is attained and a minimiser solves
  $B[u,v] = \lambda_1 (u,v)$ for every $v$. `principalEigenvalue_le_of_weak_eigen`
  places $\lambda_1$ below every weak eigenvalue and `dirichlet_principal_eigenpair` is
  the instance at $-\Delta$ on a bounded measurable domain.
  `dirichlet_principal_eigenpair_of_bounded` asks for boundedness alone because the
  Poincaré inequality names the coercivity constant.
- The later eigenvalues by constrained minimisation as
  `EllipticPdes.Sobolev.exists_higher_eigenpair`: minimising over the part of the unit
  $L^2$ sphere orthogonal to a finite orthonormal family of eigenfunctions produces
  another eigenpair with eigenvalue at least $\lambda_1$. Because
  $B[u, w_i] = \lambda_i \langle u, w_i \rangle_{L^2} = 0$ on the admissible complement,
  the multipliers of the extra constraints drop out and the minimiser is a weak
  eigenfunction of the whole space.
- The eigenvalue sequence as `EllipticPdes.Sobolev.exists_eigen_family`: for every $n$
  iterating that step gives an $L^2$-orthonormal family of $n$ weak eigenfunctions with
  $\lambda_1 \le \cdots \le \lambda_n$ in which each eigenvalue is a Rayleigh quotient
  over the vectors orthogonal to its predecessors. The recursion asks at each stage for
  a vector of nonzero $L^2$ class orthogonal to the family built so far. On a bounded
  domain that supply is the infinite dimensionality of $H_0^1(\Omega)$.
  `dirichlet_eigen_family_of_bounded` is the instance at $-\Delta$ and reads
  $0 < \lambda_1 \le \cdots \le \lambda_n$. `dirichlet_eigen_family_ball` discharges the
  last side condition on the unit ball: `orth_family_nonempty_ball` puts $n$ bumps at
  the points $((2k+1)/(2n) - 1/2)e_i$ with centres $1/n$ apart and radii $1/(2n)$.
  Because their supports are disjoint, some combination of any $m+1$ of them is
  orthogonal to any $m$ given vectors.
- The Dirichlet spectrum of the unit ball with no side hypothesis as
  `EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball`: for $d > 2$ the Rayleigh
  infimum on $H_0^1(B_1)$ is positive and attained at a minimiser that solves the weak
  eigenvalue problem. `exists_embL2_ne_zero_ball` discharges the nonemptiness the
  general statements assume and a domain of measure zero fails.
- Positivity and finite multiplicity of the Dirichlet eigenvalues as
  `EllipticPdes.Sobolev.weak_eigenvalue_pos` and
  `EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace`: every weak eigenvalue of a
  symmetric coercive form is at least $\lambda_1 > 0$. Each eigenspace of the compact
  solution operator at a nonzero eigenvalue is finite dimensional. On the unit ball
  `dirichlet_eigenvalue_pos_ball` asks for $d > 2$ and nothing else.
- The optimal constant in the Poincaré inequality as
  `EllipticPdes.Sobolev.dirichlet_poincare_sharp` with the equality case
  `dirichlet_poincare_attained`: $\lambda_1 \|u\|_{L^2}^2 \le \int |\nabla u|^2$ on all
  of $H_0^1(\Omega)$ with equality at some $u$ of unit $L^2$ norm.
- The local step of global approximation as
  `EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub`: a mollification of
  a shift converges in $L^p$ to the function as the shift and the radius go to zero
  together. That convergence lets a mollifier near the boundary see only points where
  the function is defined. Because convolution commutes with translation, the
  mollification error of the shift is the shift of the mollification error and has the
  same norm.
- Continuity of translation in $L^p$ as
  `EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub`: the $L^p$ distance between a
  function and its translate tends to zero with the translation. This bounds the shift
  into the domain of the global approximation theorem. Mathlib has the two halves
  (translation as an $L^p$ isometry and density of the continuous compactly supported
  functions) without the statement.
- The two rigid motions of the extension operator as
  `EllipticPdes.Extension.hasWeakGradOn_comp_translate` and
  `EllipticPdes.Extension.hasWeakGradOn_comp_reflect`: reflection in a coordinate
  hyperplane sends a weak gradient on a set to a weak gradient on the preimage with the
  sign negative exactly in the reflected direction. As a linear isometry the reflection
  preserves Lebesgue measure and every $L^p$ seminorm. Because the statement asks
  nothing of the set, a boundary chart can reflect across the image of a hyperplane. The
  shift into the domain of the global approximation theorem needs translation, which
  moves a weak gradient with no sign and no Jacobian.
- The third map of that operator as `EllipticPdes.Extension.hasWeakGradOn_comp_shear`:
  the shear $S(y) = y + \gamma(y) e_j$ that flattens a $C^1$ boundary sends a weak
  gradient on a set to a weak gradient on the preimage through the transpose of its
  derivative:
  $\partial_k (u \circ S) = \partial_k u \circ S + (\partial_j u \circ S)\, \partial_k \gamma$.
  Because its derivative is not an isometry, `measurePreserving_shear` reads the change
  of variables off the determinant $1$ of `det_shearDeriv`. A smooth test function
  pulled back through the shear is $C^1$ and no better, and `hasWeakGradOn_contDiffOne`
  integrates by parts against that class. For a $C^1$ chart one term of the chain rule
  scales the test function by the continuous factor $\partial_k \gamma$ and puts the
  product outside that class too. That factor does not depend on the $j$-th coordinate.
  Its mollifications are smooth and still independent of that coordinate, and
  `integral_mul_indepCoord` reads the identity off the product rule in their limit.
- The local half of the extension operator as
  `EllipticPdes.Extension.hasWeakGradOn_chartExt`: a class with a weak gradient on the
  region above the graph of a $C^1$ chart extends across that graph to a class that has
  a weak gradient on the whole space, agrees with the original above the graph and is
  bounded by twice its seminorm in every $L^p$. The three maps compose there: the shear
  pulls the region back to the half space, the even reflection crosses the interface and
  the inverse shear returns the result. Each step contributes its own half of the
  gradient. Evans assembles the same steps for a function smooth up to the boundary and
  reaches $W^{1,p}$ by density. His reflection is therefore the higher-order one that
  keeps the extension $C^1$. A statement about weak gradients throughout needs no such
  matching and uses the plain even reflection.
  `EllipticPdes.Extension.eLpNorm_chartExtGrad_le` states the bound componentwise: twice
  the seminorm of the matching component of the gradient plus four times the chart's
  bound against the normal one. The shear contributes that bound once, the reflection
  doubles it and the inverse shear contributes it again. The normal component travels
  through the shear untouched because the chart has no partial derivative in its graph
  direction.
- The hypothesis those charts satisfy as `EllipticPdes.Extension.HasC1Boundary` in the
  form Evans §C.1 states: every boundary point admits a chart consisting of an isometry
  relabelling and reorienting the axes, a direction, a $C^1$ graph of the remaining
  coordinates and a radius on whose ball the domain and the region above the graph
  agree. That is also the hypothesis of Evans §5.4 Theorem 1. The chart asks nothing of
  the gradient of its graph. Every statement about the shear needs a bound on that
  gradient, and `EllipticPdes.Extension.exists_bounded_graph` supplies it: a chart
  constrains its graph only on the ball it describes, and cutting the graph off in the
  tangential directions bounds the gradient while leaving the description alone. A
  continuous function independent of a coordinate factors through the projection that
  kills that coordinate and is bounded on a cylinder around its axis because a closed
  ball of that projection is compact. The region above a graph and the half space are
  charts at every point, and the boundary of a bounded domain is compact.
- The unit ball as an instance of that hypothesis:
  `EllipticPdes.Extension.hasC1Boundary_ball`. The half space is unbounded, and the ball
  is the first bounded domain with $C^1$ boundary in the development. The chart at a
  boundary point is the reflection in the hyperplane bisecting the point and the south
  pole. It sends the point to the pole and the ball to itself, and its graph is the
  lower hemisphere cut off in the tangential directions to make it $C^1$ on the whole
  space. On the ball of radius one half about the pole the cutoff is inactive and
  membership of the unit ball is $y_d > -\sqrt{1 - |y'|^2}$ because
  $|y|^2 = |y'|^2 + y_d^2$ with $y_d < 0$. `embW12_isCompact_ball` and
  `poincare_wirtinger_ball` are the instances with every hypothesis discharged.
- The relabelling and reorientation itself as
  `EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry`: a weak gradient moves
  through a linear isometry by the transpose of that isometry. In coordinates the
  transpose is a sum over the directions to which the isometry sends the $k$-th one.
  Because a linear isometry is its own derivative, the chain rule gives the formula at
  once. The work is in passing a finite sum through an integral, where integrability of
  the class and of its gradient enters. Reflection is the case where the sum has a
  single term and a sign.
- The first step of that patching as
  `EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter`: a cutoff supported in $W$
  sends a weak gradient on $B \cap W$ to a weak gradient on all of $B$ whose extra term
  the product rule supplies. A test function on $B$ multiplied by the cutoff is a test
  function on $B \cap W$, and both sides of the identity see only $W$ because the cutoff
  and its derivative vanish off it. `hasWeakGradOn_univ_mul_cutoff` is the case where
  the cutoff sits inside $B$ and the conclusion reaches the whole space. This statement
  covers a boundary chart's ball, which straddles $\partial\Omega$.
- The cover with which that step opens as
  `EllipticPdes.Extension.exists_finite_chart_cover`: for a bounded domain with $C^1$
  boundary finitely many charts' balls cover $\partial\Omega$ with each chart fitting at
  its centre. The boundary is closed and bounded and hence compact, and a chart at each
  of its points supplies the open cover. The chart comes back as a function on the whole
  space. That needs positive dimension: in dimension zero a chart has no direction for
  its graph and none exists. `C1Chart.fits_ball` reads a chart in the original
  coordinates because the motion is an isometry and pulls the ball about an image point
  back to the ball about the point.
- The partition of unity over that cover as
  `EllipticPdes.Extension.nonempty_boundaryPartition`: for a bounded open domain with
  $C^1$ boundary, a `BoundaryPartition` bundles the charts, their centres and a smooth
  partition of unity that is subordinate to the charts' balls together with the domain
  itself and adds to one on $\overline{\Omega}$. The index is an option: the piece
  indexed by nothing sits inside the domain away from the boundary, and the piece
  indexed by a centre sits in that chart's ball. Mathlib proves such partitions for a
  manifold, and a normed space is one over itself. `exists_smooth_partition` reads the
  smoothness of each piece back as $C^\infty$ and nothing downstream of that file meets
  a manifold.
- The local extension against which those pieces are summed as
  `EllipticPdes.Extension.exists_localExtension` and its form with a constant
  `exists_localExtension_bound`. Together they are the local step of the proof of Evans §5.4 Theorem 1: near a boundary
  point the class extends across the boundary to a class that has a weak gradient on any
  ball strictly inside the chart's ball and agrees with the original on the part of the
  domain that ball meets. The proof composes the chapter. A cutoff between two balls
  makes the class reach the whole region above the chart's graph, the rigid motion takes
  it into the coordinates of the graph, the reflection extends it across the graph and
  the motion takes the result back. Evans runs that step on a function smooth up to the
  boundary and reads the chain rule off it. Every step here works with weak gradients.
  Because the chart asks nothing of the gradient of its graph, the proof uses the
  bounded graph from `exists_bounded_graph`, whose region agrees with the chart's on
  exactly the ball in play.
- The sum that glues those pieces in the gluing step of that proof as
  `EllipticPdes.Extension.exists_extension`: on a bounded open domain with $C^1$
  boundary, a class with a weak gradient on $\Omega$ extends to one with a weak gradient
  on $\mathbb{R}^d$ agreeing with it on $\Omega$. Each piece is a local extension cut
  down afterwards by its piece of the partition. That order makes the sum agree: where a
  piece of the partition is nonzero the point lies in that chart's ball, where the local
  extension agrees with the class, and off the ball both sides vanish. The pieces
  therefore add to $u$ because the partition adds to one.
- The support clause as `EllipticPdes.Extension.exists_extension_subset`, which with the
  previous item gives clauses (i) and (ii) of Evans §5.4 Theorem 1: any open set
  containing the closure of the domain admits a smooth cutoff equal to one on that
  closure, and multiplying by it moves the support inside without disturbing the
  agreement.
- The norm bound of clause (iii) as
  `EllipticPdes.Extension.exists_extension_subset_bound`, which completes Evans §5.4
  Theorem 1: one constant that depends on the domain and the exponent and is quantified
  before the class bounds the extension and its gradient in every $L^p$ seminorm by the
  class and its gradient over $\Omega$. The chart, its bounded graph, its two cutoffs,
  the partition of unity and the supremum of each piece and of its partials depend on
  $\Omega$ alone. `exists_localExtension_bound` therefore fixes them before the class
  appears and `exists_extension_bound` sums the local constants over the finitely many
  pieces. The five estimates the chain threads are the cutoff's supremum, the rigid
  motion, the reflection, the shear and the sum over the coordinates the motion mixes.
- The operator itself as `EllipticPdes.Extension.extLinear` and
  `EllipticPdes.Extension.exists_extLinear` in the form Evans states §5.4 Theorem 1: one
  $\mathbb{R}$-linear map and one constant serving every class. The named forms
  `localExtension_bound`, `extension_bound` and `extension_subset_bound` state the three
  clauses against `EllipticPdes.Extension.extSubsetFun` in place of an existential. The
  three earlier `exists_` forms are corollaries of them with unchanged statements.
  Linearity is available because the partition, the charts, the bounded graphs, the
  radii and the two cutoffs are all chosen from the domain alone before any class
  appears. What is left is multiplication by fixed functions, precomposition with fixed
  maps and a finite sum. The map acts on `EllipticPdes.Extension.SobolevPair`, which
  pairs a class with a candidate gradient because this development relates the two
  through `HasWeakGradOn` and has no bundled Sobolev space. The bound is therefore
  stated on the pair in place of an operator norm and at every exponent.
- The operator between the Sobolev spaces themselves as
  `EllipticPdes.Extension.exists_extW12` in the form of Evans §5.4 Theorem 1 at
  $p = 2$: a bounded linear map from the graph space `W12` of the domain (the
  $H^1(\Omega)$ of this development) to the graph space of the whole space that agrees
  with the element on the domain in the function and gradient coordinates, has function
  coordinate vanishing outside the given open set and is bounded by a constant times the
  norm. The map on classes is the map on representatives. It descends because it is
  linear and bounded by the seminorms over the domain: two representatives of one class
  differ by a pair of seminorm zero and their images therefore differ by a function of
  seminorm zero. That closes the difference of space the previous item records.
- Global approximation by functions smooth up to the boundary as
  `EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn` (§5.3.3 Theorem 3 of
  Evans at order one): on a bounded domain with $C^1$ boundary a class with an $L^p$
  weak gradient is the $W^{1,p}(\Omega)$ limit of smooth compactly supported functions
  on $\mathbb{R}^d$. Evans shifts the class into the domain near each boundary point,
  mollifies and patches with a partition of unity. The extension operator makes the
  shift unnecessary: the mollifications of the extension converge to it in
  $L^p(\mathbb{R}^d)$ together with their gradients, and the extension agrees with the
  class on $\Omega$. `exists_smooth_tendsto_of_mem_W12` is the statement at $p = 2$ for
  the graph space `W12`: density of the smooth functions in $H^1(\Omega)$.
- Rellich-Kondrachov on $H^1(\Omega)$ as `EllipticPdes.Sobolev.embW12_isCompact` (§5.7
  Theorem 1 of Evans at $p = q = 2$): on a bounded domain with $C^1$ boundary the
  embedding of the graph space `W12` into $L^2(\Omega)$ is compact. `embL2_isCompact` is
  the statement on $H_0^1(\Omega)$ with a proof that extends by zero. An element of
  $H^1(\Omega)$ extended by zero jumps at the boundary and loses the translation modulus
  that the Fréchet-Kolmogorov criterion requires. The extension operator restores the
  modulus, which `transL2_toLp_sub_le_of_hasWeakGradOn_univ` states for a whole-space
  class with a weak gradient, and restriction to $\Omega$ is Lipschitz.
- Poincaré's inequality with the mean subtracted as
  `EllipticPdes.Sobolev.poincare_wirtinger` (§5.8.1 Theorem 1 of Evans at $p = 2$): on a
  bounded connected open domain with $C^1$ boundary one constant bounds the $L^2$
  distance of every element of $H^1(\Omega)$ from its mean by the $L^2$ norm of its
  gradient. The proof is Evans's contradiction argument: a sequence of unit $L^2$ norm,
  zero mean and vanishing gradient has an $L^2$-convergent subsequence by
  Rellich-Kondrachov on $H^1(\Omega)$. The graph space is closed and the limit therefore
  has zero weak gradient. `EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero` makes
  the limit constant on the connected domain and its zero mean makes it zero, which
  contradicts its unit norm. That lemma is Evans's Problem 11 of Chapter 5: the
  mollifications of the class have zero classical gradient on any ball whose double lies
  in the domain. Each is therefore constant there, as is their $L^1$ limit because the
  constants form a closed line. The constant of a ball is locally constant in its centre
  and hence takes one value on a preconnected set, and a countable subcover puts the
  class equal to it almost everywhere.
- Poincaré's inequality on a ball as `EllipticPdes.Sobolev.poincare_ball` (§5.8.1
  Theorem 2 of Evans at $p = 2$): one constant depending on the dimension alone bounds
  the $L^2$ distance of a class on any ball from its mean over the ball by the radius
  times the $L^2$ norm of its gradient. The unit-ball case is the previous item, and the
  affine map $y \mapsto ry + x$ takes it onto the ball. That map is measure-preserving
  from the unit ball to the ball with Lebesgue measure scaled by $r^{-d}$. The mean is
  therefore unchanged, the weak gradient picks up the factor $r$ and the seminorm factor
  $r^{-d/2}$ cancels between the two sides.
- The chain rule for weak gradients as `EllipticPdes.Embedding.hasWeakGradOn_comp`
  (Lemma 7.5 of Gilbarg and Trudinger): on an open set the composition of a $C^1$
  function $f$ with bounded derivative and a locally integrable class $u$ with locally
  integrable weak gradient has the weak gradient $f'(u)\,\nabla u$. The class is
  mollified on a compact neighbourhood of the support of the test function, the
  classical identity holds for each mollification, and the two sides pass to the limit
  with the gradient side along a subsequence converging almost everywhere. Their Lemma
  7.6 follows as `EllipticPdes.Embedding.hasWeakGradOn_posPart` through the $C^1$
  functions $\sqrt{(t^+)^2 + \varepsilon^2} - \varepsilon$: the weak gradient of $u^+$
  is $\nabla u$ where $u > 0$ and zero elsewhere.
  `EllipticPdes.Embedding.hasWeakGradOn_negPart` and
  `EllipticPdes.Embedding.hasWeakGradOn_abs` give the clauses for $u^-$ and $|u|$, and
  `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn` is their Lemma 7.7:
  the weak gradient vanishes almost everywhere on every level set.
- The weak maximum principle as `EllipticPdes.Sobolev.weak_maximum_principle` (Theorem
  8.1 of Gilbarg and Trudinger) in the transport-free case their proof singles out with
  nonnegative zeroth-order coefficient on a bounded open set. The boundary inequality
  $u \le k$ on $\partial\Omega$ is their membership of $(u - k)^+$ in $H^1_0(\Omega)$,
  and the conclusion is $u \le k$ almost everywhere for every such $k \ge 0$. The
  subsolution inequality is taken against every nonnegative element of $H^1_0(\Omega)$
  in the form their proof uses. Against $v = (u - k)^+$ the zeroth-order term is
  nonnegative, the principal term is the energy of $v$ by the chain rule for the
  positive part, ellipticity makes the gradient of $v$ vanish and the Poincaré
  inequality on $H^1_0$ of the bounded domain makes $v$ vanish. The general case with a
  transport term runs through the Sobolev inequality and a limit in $k$ and appears two
  items below.
- Truncation in $H^1_0$ as `EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const`: for
  $V$ in $H^1_0(\Omega)$ and $k \ge 0$, the truncation $(v - k)^+$ with the gradient of
  $v$ on $\{v > k\}$ and zero elsewhere is again in $H^1_0(\Omega)$. The proof of
  Theorem 8.1 asserts this membership for its test function. By mollification a class
  with $L^2$ weak gradient and compact support in $\Omega$ lies in $H^1_0(\Omega)$ as
  `EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport` states by applying Evans's §5.3.1
  Theorem 1. The truncations of approximating test functions keep compact support
  because $k \ge 0$ and converge to the truncation of the limit. Their gradient
  coordinates converge along a subsequence almost everywhere by dominated convergence,
  and the level set $\{v = k\}$ contributes nothing because the weak gradient vanishes
  there. With it the principle applies to every subsolution in $H^1_0(\Omega)$ as
  `EllipticPdes.Sobolev.weak_maximum_principle_H01`, and their Corollary 8.2 on
  uniqueness of the generalised Dirichlet problem follows as
  `EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01` by applying the principle to the
  solution and to its negative.
- The weak maximum principle with a transport term as
  `EllipticPdes.Sobolev.weak_maximum_principle_transport` (Theorem 8.1 of Gilbarg and
  Trudinger) with their coefficients $c^i$ present in dimension at least two. Testing
  against $v = (u - k)^+$ bounds the energy of $v$ by the transport bound times the
  gradient norm of $v$ times the $L^2$ norm of $v$ over the set $\Gamma_k$ where $u > k$
  and the gradient does not vanish. Ellipticity, the Sobolev inequality on $H^1_0$ and
  Hölder's inequality then bound the measure of $\Gamma_k$ below by a constant
  independent of $k$ whenever $v \ne 0$. In dimension two the Sobolev inequality is the
  embedding into $L^4$ through the inequality at $p = 3/2$ as
  `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_two`, which is the remark on $n = 2$ in
  their proof. As $k$ increases to the supremum $T$ of the levels with nonzero
  truncation, the sets $\Gamma_k$ shrink into $\{u \ge T\}$ with nonvanishing gradient.
  That set is null because $\{u > T\}$ is null by the choice of $T$ and the gradient
  vanishes almost everywhere on $\{u = T\}$. No level above the boundary value therefore
  has a nonzero truncation. The truncations at every level above the boundary value come
  from the truncation lemma as `EllipticPdes.Sobolev.exists_truncation_mem_H01`.
- The classical weak maximum principle as
  `EllipticPdes.Classical.weak_maximum_principle` (Evans's §6.4.1 Theorem 1 and Gilbarg and
  Trudinger's Theorem 3.1): a function $C^2$ on a bounded open
  set and continuous on its closure with $Lu \le 0$ for the non-divergence-form operator
  $Lu = -a^{ij} u_{x_i x_j} + b^i u_{x_i}$ with symmetric uniformly elliptic $a$ and
  bounded $b$ attains its maximum over the closure on the boundary. At an interior local
  maximum the gradient vanishes and the Hessian is negative semidefinite as
  `EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax` shows through the
  one-dimensional second-order test along lines. The trace inequality
  `EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef` proved through the spectral
  theorem makes the principal part nonnegative there. A strict subsolution therefore has
  no interior maximum, and $u + \varepsilon e^{\lambda x_1}$ is a strict subsolution for
  $\lambda$ large. The supersolution clause is
  `EllipticPdes.Classical.weak_minimum_principle`. Theorem 2 with $c \ge 0$ and the
  positive part on the boundary is
  `EllipticPdes.Classical.weak_maximum_principle_of_nonneg` through Theorem 1 on the set
  where $u > 0$, and its supersolution clause is
  `EllipticPdes.Classical.weak_minimum_principle_of_nonneg`. Three corollaries follow:
  the strict maximum principle that opens Gilbarg and Trudinger's proof of Theorem 3.1 as
  `EllipticPdes.Classical.not_isLocalMax_of_nondivOp_neg`, Gilbarg and Trudinger's
  comparison principle 3.3 as `EllipticPdes.Classical.comparison_principle`, and the
  bound of a solution by its boundary values in the second clause of their Corollary 3.2
  as `EllipticPdes.Classical.abs_le_of_nondivOp_eq_zero`.
- Hopf's lemma and the strong maximum principle as `EllipticPdes.Classical.hopf_lemma`
  and `EllipticPdes.Classical.strong_maximum_principle` (Evans's §6.4.2 Lemma and
  Theorem 3 and Gilbarg and Trudinger's Lemma 3.4 and Theorem 3.5) in both clauses: the
  zeroth-order coefficient is nonnegative and bounded with $c\,u(x^0) \ge 0$. That
  covers $c = 0$, and `EllipticPdes.Classical.strong_maximum_principle_of_nonneg` covers
  $c \ge 0$ with a nonnegative maximum. The barrier
  $v = e^{-\lambda|x - y|^2} - e^{-\lambda r^2}$ is a subsolution on the annulus
  $r/2 < |x - y| < r$ for $\lambda$ large because the zeroth-order term is at most the
  bound on $c$ times the exponential. It vanishes on the outer sphere and is positive on
  the inner one. By the weak maximum principle with $c \ge 0$ the function
  $u + \varepsilon v - u(x^0)$ is nonpositive on the annulus, and its one-sided
  derivative at $x^0$ along the inward radius is nonpositive, which forces a positive
  outward derivative of $u$. For the strong principle connectedness gives the set where
  $u$ is below its maximum a frontier point inside the domain. The largest ball about a
  nearby point of that set touches the level set of the maximum at an interior maximum
  where Hopf's lemma nonetheless gives a nonzero gradient. The corollaries of the strong
  maximum principle follow. `EllipticPdes.Classical.hopf_lemma_of_zero` and
  `EllipticPdes.Classical.strong_maximum_principle_of_zero` give the clauses with $c$ of
  any sign and a zero extremal value by replacing $c$ with its positive part, which
  lowers the image on a nonpositive function.
  `EllipticPdes.Classical.avoidance_principle` is the avoidance principle,
  `EllipticPdes.Classical.eq_of_eq_of_fderiv_eq` is tangency at a boundary point with an
  interior sphere and `EllipticPdes.Classical.dirichlet_unique` is uniqueness for the
  Dirichlet problem. `EllipticPdes.Classical.neumann_unique` is uniqueness up to a
  constant for the Neumann problem: the difference of two solutions attains its maximum
  over the closure, an interior nonnegative maximum makes it constant and a boundary
  maximum contradicts Hopf's lemma through the vanishing normal derivative.
- The a priori bound from the maximum principle as
  `EllipticPdes.Classical.apriori_bound_sub` and
  `EllipticPdes.Classical.apriori_bound_abs` (Gilbarg and
  Trudinger's Theorem 3.7) for a domain between two parallel planes a distance $D$
  apart: with $c \ge 0$ and $|f| \le F$ a solution of $Lu = f$ is bounded by the
  boundary supremum of $|u|$ plus $(e^{(B/\theta + 1) D} - 1) F/\theta$. The comparison
  function $\sup u^+ + (F/\theta)(e^{\alpha D} - e^{\alpha (x_1 - m)})$ at
  $\alpha = B/\theta + 1$ has image at least $F$ under $L$ and the comparison principle
  applies to it.
- The maximum principles for subharmonic, superharmonic and harmonic functions in Gilbarg and
  Trudinger's Theorems 2.2 and 2.3 as
  `EllipticPdes.Classical.strong_maximum_principle_subharmonic`,
  `EllipticPdes.Classical.weak_maximum_principle_subharmonic` and their companions, and
  their Theorem 2.4, uniqueness for the Dirichlet problem, as
  `EllipticPdes.Classical.dirichlet_unique_harmonic`: the Laplacian as the sum of the
  second coordinate partials is the negative of the operator with the identity as
  coefficient matrix and no lower-order terms.
- The Gagliardo-Nirenberg-Sobolev inequality on a bounded domain with $C^1$ boundary as
  `EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain`. It is the single rung
  the order-$k$ embedding iterates: a class on $\Omega$ with an $L^p$ weak gradient lies
  in $L^{p'}(\Omega)$ at $1/p' = 1/p - 1/d$ with a constant. On a ball the same
  inequality shrinks the ball because the cutoff feeding the whole-space statement is
  one only inside. The extension operator supplies that cutoff once and keeps the
  estimate on $\Omega$ throughout.
- The Sobolev ladder on that domain as
  `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`: the rung iterated
  $s$ times with no ball shrinking. One constant takes a uniform $L^{p_0}$ bound on the
  family to an $L^q$ bound on the member.
- Hölder continuity up to the boundary as
  `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain`: the ladder
  reaches an exponent above the dimension, the extension puts the member and its first
  derivatives on the whole space, and Morrey on a ball containing $\overline{\Omega}$
  produces the representative, whose Hölder seminorm on $\overline{\Omega}$ one constant
  bounds by the uniform $L^{p_0}$ bound.
- The representatives of clause (ii) as classical derivatives:
  `EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain` and
  its two clause forms `exists_const_contDiffOn_holderOnWith_domain_ideal` and
  `exists_const_contDiffOn_holderOnWith_domain_free`. One family of representatives
  serves every index at once, and the derivative of each representative is the next. The
  member is therefore $n$ times continuously differentiable on $\Omega$ whenever the
  supply leaves $n$ orders above it. That is what
  $u \in C^{k-1-\lfloor n/p \rfloor, \gamma}(\overline{\Omega})$ asserts, and the
  per-member statement gives only a Hölder representative of each derivative separately.
- Both clauses of the order-$k$ Sobolev embedding on a bounded $C^1$ domain as
  `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal`,
  `exists_const_holderOnWith_domain_ideal` and `exists_const_holderOnWith_domain_free`.
  Clause (i) lands on the exponent $1/q = 1/p - k/n$ under the strict rung condition
  $pk < n$. Clause (ii) gives on $\overline{\Omega}$ and at every order up to
  $k - 1 - \lfloor n/p \rfloor$ the Hölder exponent $\lfloor n/p \rfloor - n/p + 1$ when
  $n/p$ is not an integer and any $\gamma \in (0,1)$ when it is. It bounds the supremum
  and the Hölder seminorm together, which make up the whole $C^{0,\gamma}$ norm. A
  member of $W^{k,p}(\Omega)$ is read as a family closed under weak differentiation with
  a depth function in place of $D^\alpha u$. The interior statements use the same
  vocabulary.
- Both cases of the order-$k$ embedding off `p = 2`. Case (ii) is
  `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general`: the ladder runs
  for $s$ rungs from $L^{p_0}$ and Morrey reads the Hölder exponent off the exponent it
  reaches. `morreyExponent_eq_ladder` identifies that exponent as $s + 1 - d/p_0$, which
  at $s = \lfloor d/p_0 \rfloor$ is the $\lfloor n/p \rfloor + 1 - n/p$ of Evans §5.6.3
  Theorem 6. When $d/p_0$ is an integer the ladder reaches every finite exponent and the
  Hölder exponent is free in $(0,1)$. That is the other case the statement separates.
- The Sobolev ladder off `p = 2` as
  `EllipticPdes.Embedding.memLp_of_gradClosed_general`: the rung iterates from any base
  exponent $p_0 \in [1, \infty)$, and `memLp_of_gradClosed_general_ideal` lands on the
  exponent $1/q = 1/p_0 - s/d$ that Evans §5.6.3 Theorem 6 clause (i) names under his
  strict rung condition $p_0 s < d$. Below $p_0 = 2$ a target can sit under the
  conjugate exponent $d/(d-1)$, where the rung from $p_0$ overshoots and the exponent is
  lowered onto the target by the finiteness of the ball's measure.
- The two general Sobolev estimates with their constants as
  `EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep` and
  `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound`: one
  constant quantified before the family takes a uniform $L^2$ bound over the outer ball
  to the $L^q$ bound and to the Hölder seminorm on the inner one.
- The Hölder exponent in even dimension as
  `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even`: any $\gamma$ in the
  interval $(0,1)$ that Evans §5.6.3 Theorem 6 leaves open when $n/p$ is an integer. In
  odd dimension the reciprocal the ladder lands on caps the exponent at $2d$ and forces
  $\gamma = 1/2$.

The embedding of $H_0^1(\Omega)$ runs the Gagliardo-Nirenberg-Sobolev inequality on test
functions and passes it to their closure. `poincare_H01` makes that passage by
continuity because its estimate is a closed condition on a continuous function of the
graph. The two sides of the Sobolev estimate sit at different exponents and leave lower
semicontinuity in place of continuity: convergence in $H^1$ gives convergence of the
function coordinates in $L^2(\Omega)$ and hence in measure, and Fatou's lemma along an
almost-everywhere convergent subsequence takes the bound to the limit. Because the
transfer reads the test-function estimate as a hypothesis at an arbitrary exponent, each
variant of the inequality reaches $H_0^1(\Omega)$ by supplying it.

Compactness at those exponents refines the $L^2$ statement without repeating its proof.
Evans mollifies, bounds the $L^1$ error uniformly over a bounded family,
interpolates and finishes with Arzelà-Ascoli. The first and last moves give compactness at
the lower exponent, which `embL2_isCompact` already supplies from a translation modulus
and without an extension operator. The interpolation does the rest: a finite net of the
unit ball's image in $L^2(\Omega)$ is a net in $L^q(\Omega)$ at the radius the estimate
names once the $L^{2^{\star}}$ seminorms of the differences are bounded on the ball.
Below $L^2$ no interpolation is needed because the embedding factors through the $L^2$
one along the inclusion a finite measure supplies.

`EllipticPdes.Embedding.not_isCompactOperator_critEmb` shows that range is optimal: at
$2^{\star}$ itself the embedding is bounded and not compact. Dilating by $\lambda$
scales the $L^p$ seminorm by $\lambda^{d/p}$ and each derivative by $\lambda^{-1}$
(`EllipticPdes.Analysis.eLpNorm_comp_smul` and
`EllipticPdes.Embedding.eLpNorm_partialD_dilate`). The renormalised dilates
$\lambda^{1-d/2}\varphi(\cdot/\lambda)$ of a bump therefore keep their $L^{2^{\star}}$
norm and their gradient norm while losing their $L^2$ norm, and their images have no
convergent subsequence.

The Hölder estimate chains the $H^2$ estimate through Morrey's inequality on a ball.
Supporting layers supply Morrey's inequality itself, the Gagliardo-Nirenberg-Sobolev
bootstrap `exists_eLpNorm_sobolevConj_le` in general dimension and at a general exponent
pair, Campanato's characterisation of Hölder continuity with its converse and the
Caccioppoli inequality.

Out of $L^2$ data one Sobolev step reaches Morrey only below dimension four:
$1/p' = 1/p - 1/d$ gives $p' > d$ only for $p > d/2$, and the window $d/2 < p \le 2$ is
empty once $d \ge 4$. Iterating the step at one weak derivative per rung reaches every
dimension. The iteration runs on a family closed under weak differentiation: an index
type, a function per index and a successor naming the weak derivatives of that function.
One induction therefore climbs with no separate induction on the order of
differentiation.

Two ladders are built on that family. `memLp_of_gradClosed` climbs at the half step
$1/(2d)$ and reaches $L^{2d}$ after $d - 1$ rungs with every intermediate reciprocal
positive. It runs where weak derivatives of every order are available, and its consumer
is `interior_smooth`. `memLp_of_gradClosed_fullStep` climbs at the full step $1/d$ and
reaches the same exponent after $\lfloor d/2 \rfloor$ rungs and bounds the supply with a
depth function. Its consumer is `exists_contDiffOn_holder_ball`, where the supply is
finite. The full step lands on the reciprocal $0$ when $d$ is even. The rung form
`exists_eLpNorm_sobolevConj_le_of_le` covers that case by taking its hypothesis in $L^q$
for any $q \ge p$ while concluding at the conjugate of $p$. Smoothness in the interior
is the half-step ladder followed by
`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn`, which turns a
continuous weak gradient back into a classical derivative.

Differentiating the `L^q` constraint is the one analytic step the direct method needs
beyond compactness. The integrand's derivative in `t` is bounded on $|t| < 1$ by
$q(|u| + |v|)^{q-1}|v|$. Its first factor sits in $L^{q/(q-1)}$ and its second in $L^q$.
Hölder's inequality therefore supplies a dominating function, and mathlib's
`hasDerivAt_abs_rpow` supplies the pointwise derivative at every point including the
origin. Fermat's theorem then applies to
$t \mapsto \|U + tV\|^2 - \lambda\|T(U + tV)\|_{L^q}^2$, which vanishes at $t = 0$ and
is nonnegative everywhere because rescaling $U + tV$ back to the constraint set is
admissible wherever its image is nonzero. Homogeneity of the `L^q` norm is what makes
that rescaling available and replaces the implicit function theorem Evans applies to a
general constraint. The same argument runs at any symmetric positive semidefinite form
in place of the squared norm because it uses only the quadratic expansion of $Q(U + tV)$
and the degree-two homogeneity of $Q$:
`EllipticPdes.Analysis.euler_lagrange_of_quadratic_min` is that statement, and at the
Dirichlet form it gives the equation $-\Delta u = \lambda|u|^{q-2}u$ with no lower-order term.

The eigenvalue chapter has two independent routes to the Dirichlet spectrum.
`solOp_spectral` runs the spectral theorem for the compact self-adjoint solution
operator and produces the whole orthonormal basis of eigenfunctions with no formula for
any eigenvalue. The variational route names the first one through the direct method of
`exists_minimiser_of_lt` at a quadratic constraint. Weak lower semicontinuity of the
form is there the expansion of $0 \le B[u_k - w, u_k - w]$ against
$B[u_k, w] \to B[w, w]$, and the Euler-Lagrange step is in one variable because the map
$t \mapsto B[u + tv, u + tv] - \lambda_1\|u + tv\|_{L^2}^2$ is a quadratic that vanishes
at $t = 0$ and is nonnegative everywhere. Repeating the step against the eigenfunctions
already found names every later eigenvalue the same way. `exists_bilin_minimiser` states
the direct method once for a symmetric coercive form and any compact constraint map into
a normed space, and both the Rayleigh problem and the semilinear problem are instances
of it. Positivity of the minimiser and simplicity of $\lambda_1$ make up the rest of
Evans §6.5.1 Theorem 2. Both need the maximum principle and are open.

Boundary $H^2$ regularity has its foundations in place and its headline estimate
open: the half-ball geometry, tangential difference quotients with their $H_0^1$
admissibility, and the weak quotient rule dividing a $C^1$ weight out of a weak
derivative. The boundary estimate itself is not reached, and Schauder
$C^{k,\alpha}$ estimates remain a roadmap item.

</details>

## Dependency chain

The analytic content of the solvability theory reduces to the one-dimensional Poincaré
inequality. From there: the slab inequality along any unit vector, Poincaré on a bounded
set by density in $H_0^1$, coercivity of $B$ and Lax-Milgram for existence and
uniqueness. Gårding's inequality makes every operator an instance of the abstract
shifted-coercive form `GardingForm` on a Hilbert space with a compact embedding, and the
Fredholm alternative, the exceptional set, the resolvent bound and the spectral theorem
are proved once at that level. Rellich-Kondrachov on a bounded set of `E` is transported
from the coordinate theorem through an orthonormal basis.

## Layout

- `lean/` the formalisation. A standalone lake project pinned to Lean
  `v4.35.0-rc3`.
- `lean/AxiomAudit.lean` checks the axiom set of each headline result with
  `assert_classical_axioms` and builds as a target of its own.
- `lean/Challenge.lean` and `lean/Solution.lean` are the Palomar submission pair for the
  six solvability results of Evans §6.2 together with `lean/comparator.json` and
  `lean/formalization.yaml`.

## Build

```bash
cd lean && lake build      # includes the axiom pins in AxiomAudit.lean
cd lean && lake lint       # environment-level linter
cd lean && lake build Challenge Solution   # the Palomar pair
```

CI runs these on every push. It builds from a clean clone, asserts the library is free
of `sorry` and pins every headline result to the axioms `propext`, `Classical.choice`
and `Quot.sound` through `AxiomAudit.lean`, where `assert_classical_axioms` fails the
build on any other axiom.

CI then re-checks the library with
[`con-leche`](https://github.com/leanprover/con-leche), an external checker for Lean's
export format whose own consistency is proven in Lean: an accepted stream declares no
constant of type `False`. It reads the dependency cone of every declaration
`AxiomAudit.lean` lists, admits `propext`, `Classical.choice` and `Quot.sound` alone and
rejects a stream that uses any other axiom including `sorryAx`. The audit reaches that
conclusion through the elaborator that produced the proofs, and con-leche reaches it
through a second implementation with a machine-checked consistency proof.

## Palomar

`lean/Challenge.lean` states six results of Evans §6.2 in Mathlib vocabulary alone: the
Gårding inequality, existence and uniqueness for a nonnegative zeroth-order coefficient,
the Fredholm alternative, solvability against the transpose problem, the discrete set of
exceptional shifts and boundedness of the inverse. It inlines the graph encoding of
$H_0^1(\Omega)$, reads the bilinear form off the graph coordinates as a sum of integrals
and leaves each statement `sorry`. Because every result but the Gårding inequality is
stated for a bounded open $\Omega$, the proofs discharge the Rellich-Kondrachov compact
embedding and do not assume it. Openness gives those five conclusions content: a test
function has `tsupport φ ⊆ Ω`, which on a set of positive measure with empty interior
forces every test function to vanish and $H_0^1(\Omega)$ to be zero.
`lean/Solution.lean` states the same six statements under the same names and proves them
from the library.

Because Comparator looks a theorem up by name in both modules, `Solution.lean` restates
the definitions and does not import `Challenge.lean`. `verify/palomar_sync.py` keeps the
two copies identical character for character and runs in CI. Drift there would produce
two statements that both elaborate and differ, and the build would not catch it.

The six `sorry`s in `Challenge.lean` are the placeholders Comparator requires. Nothing
under `EllipticPdes/` has one, and `Solution.lean` has none either: each of its six
results pins its own axiom set with `#guard_msgs` and a `sorryAx` reaching any of them
fails the build.

The pair at commit `ae5e339` is registered in the [Palomar registry](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-15-000012&version=1) as
`PALOMAR-2026-10-15-000012` version 1.

## Toolchain

Lean `v4.35.0-rc3` with Mathlib `v4.35.0-rc3`.

## Licence

Apache-2.0.
