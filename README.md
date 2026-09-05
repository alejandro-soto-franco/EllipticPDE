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
`sorry` in the library. Declarations are named without their `EllipticPdes.`
prefix.

| Result | Declaration |
|---|---|
| Existence and uniqueness of the weak solution | `Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded` |
| Gårding inequality | `Sobolev.FullEllipticOp.garding` |
| Complete Fredholm alternative: kernel, index and solvability | `Sobolev.FullEllipticOp.fredholm_alternative` |
| Resolvent bound | `Sobolev.FullEllipticOp.resolvent_bound` |
| Spectral compactness | `Sobolev.spectrum_compact_operator` |
| Interior $H^2$ regularity | `Regularity.interior_H2_estimate` |
| Higher interior regularity at every order | `Regularity.higher_interior_regularity` |
| Infinite differentiability in the interior | `Regularity.interior_smooth` |
| The pointwise equation of the smooth representative | `Regularity.weakSolution_ae_eq_of_contDiffOn` |
| Classical solvability in the interior | `Regularity.exists_weakSolution_interior_classical` |
| Interior Hölder continuity at exponent $\tfrac12$, dimensions one to three | `Embedding.interior_holder_estimate_one` |
| Interior Hölder continuity of finite order, every dimension | `Regularity.exists_contDiffOn_holder_ball` |
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
| The shear, the third map it runs on | `Extension.hasWeakGradOn_comp_shear` |
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
| The norm bound, clause (iii) | `Extension.exists_extension_subset_bound` |
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
| Hopf's lemma | `Classical.hopf_lemma` |
| The strong maximum principle | `Classical.strong_maximum_principle` |
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
  $k + 1 + \lfloor n/2 \rfloor \le m$. This is case (ii) of the order-$k$ Sobolev
  embedding at $p = 2$,
- the pointwise equation of the smooth representative, as
  `EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn`: a weak solution
  whose function coordinate has a $C^2$ representative on an open subset of
  the domain satisfies $-\sum_{i,j}\partial_j(a^{ij}\partial_i u) +
  \sum_i b^i \partial_i u + c u = f$ there almost everywhere, the diffusion
  being $C^1$. The classical gradient of the representative is a weak gradient
  on the open set, so by uniqueness it is the weak gradient of the solution
  there, the weak formulation tested against a function supported in the set
  is integrated by parts once more, and the fundamental lemma of the calculus
  of variations, Guo's Lemma I.2.4, makes the residual vanish.
  `exists_weakSolution_interior_classical` composes it with
  `exists_weakSolution_interior_smooth`, so classical solvability in the
  interior is now closed on both halves, regularity and equation,
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
- the third map that operator runs on, as
  `EllipticPdes.Extension.hasWeakGradOn_comp_shear`: the shear
  $S(y) = y + \gamma(y) e_j$ that flattens a $C^1$ boundary sends a weak
  gradient on a set to a weak gradient on the preimage, the transpose of its
  derivative applied to the gradient, so
  $\partial_k (u \circ S) = \partial_k u \circ S + (\partial_j u \circ S)\,
  \partial_k \gamma$. Its derivative is not an isometry, so
  `measurePreserving_shear` reads the change of variables off the determinant
  $1$ of `det_shearDeriv`, and a smooth test function pulled back through it is
  $C^1$ and no better, which is the class `hasWeakGradOn_contDiffOne` integrates
  by parts against. One term of the chain rule scales the test function by
  $\partial_k \gamma$, continuous and no better for a $C^1$ chart, so the
  product sits outside that class too. That factor does not depend on the $j$-th
  coordinate, mollification leaves it independent of that coordinate and makes
  it smooth, and `integral_mul_indepCoord` reads the identity off the product
  rule in the limit,
- the local half of the extension operator, as
  `EllipticPdes.Extension.hasWeakGradOn_chartExt`: a class with a weak gradient
  on the region above the graph of a $C^1$ chart extends across that graph to a
  class with a weak gradient on the whole space, agreeing with the original above
  the graph and bounded by twice its seminorm in every $L^p$. The three maps
  compose there: the shear pulls the region back to the half space, the even
  reflection crosses the interface, and the inverse shear returns the result,
  each step contributing its own half of the gradient. Guo assembles the same
  steps for a function smooth up to the boundary and reaches $W^{1,p}$ by
  density, which is why his reflection is the higher-order one that keeps the
  extension $C^1$; a statement about weak gradients throughout needs no such
  matching, and the plain even reflection serves. The bound is componentwise,
  as `EllipticPdes.Extension.eLpNorm_chartExtGrad_le`: twice the seminorm of
  the matching component of the gradient plus four times the chart's bound
  against the normal one, the shear contributing that bound once, the
  reflection doubling, and the inverse shear contributing it again. The normal component
  travels through the shear untouched, the chart having no partial derivative
  in the direction it is a graph in,
- the hypothesis those charts satisfy, as
  `EllipticPdes.Extension.HasC1Boundary`, in the form Evans §C.1 states it:
  every boundary point admits a chart, which is an isometry relabelling and
  reorienting the axes, a direction, a $C^1$ graph of the remaining
  coordinates, and a radius on whose ball the domain and the region above the
  graph agree. That is also the hypothesis of Guo's Theorem III.2.2. The chart
  asks nothing of the gradient of its graph, which every statement about the
  shear needs, and `EllipticPdes.Extension.exists_bounded_graph` supplies the
  bound instead: a chart constrains its graph only on the ball it describes, so
  cutting the graph off in the tangential directions leaves the description
  alone and bounds the gradient. A continuous function independent of a
  coordinate is bounded on a cylinder around that coordinate's axis, factoring
  through the projection that kills it, and a closed ball of that projection is
  compact. The region above a graph and the half space are charts at every
  point, and the boundary of a bounded domain is compact,
- the unit ball as an instance of that hypothesis, as
  `EllipticPdes.Extension.hasC1Boundary_ball`. Until it, the half space was the
  only domain shown to have $C^1$ boundary, and the half space is not bounded,
  so no theorem on a bounded domain with $C^1$ boundary had a domain to be
  applied to. The chart at a boundary point is the reflection in the hyperplane
  bisecting the point and the south pole, which sends the point to the pole and
  the ball to itself, with the graph of the lower hemisphere cut off in the
  tangential directions so that it is $C^1$ on the whole space; on the ball of
  radius one half about the pole the cutoff is inactive and membership of the
  unit ball is $y_d > -\sqrt{1 - |y'|^2}$, since $|y|^2 = |y'|^2 + y_d^2$ with
  $y_d < 0$. `embW12_isCompact_ball` and `poincare_wirtinger_ball` are the
  instances with every hypothesis discharged,
- the relabelling and reorientation itself, as
  `EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry`: a weak gradient
  moves through a linear isometry by the transpose of that isometry, which in
  coordinates is the sum over the directions it sends the $k$-th one to. A
  linear isometry is its own derivative, so the chain rule gives the formula at
  once; the work is that a finite sum has to travel through an integral, which
  is where integrability of the class and of its gradient enters. Reflection is
  the case where the sum has a single term and a sign,
- the first step of that patching, as
  `EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter`: a cutoff supported in
  $W$ sends a weak gradient on $B \cap W$ to a weak gradient on all of $B$, with
  the product rule supplying the extra term. A test function on $B$ multiplied by
  the cutoff is a test function on $B \cap W$, and both sides of the identity see
  only $W$, the cutoff and its derivative vanishing off it.
  `hasWeakGradOn_univ_mul_cutoff` is the case where the cutoff sits inside $B$
  and the conclusion reaches the whole space; a boundary chart's ball straddles
  $\partial\Omega$ instead, which is what this covers,
- the cover that step opens with, as
  `EllipticPdes.Extension.exists_finite_chart_cover`: for a bounded domain with
  $C^1$ boundary, finitely many charts' balls cover $\partial\Omega$, each with
  its chart fitting at the centre. The boundary is closed and bounded, hence
  compact, and a chart at each of its points supplies the open cover. The chart
  comes back as a function on the whole space, which asks the dimension to be
  positive: in dimension zero a chart has no direction to take its graph in and
  none exists. `C1Chart.fits_ball` reads a chart in the original coordinates,
  the motion being an isometry and so pulling the ball about an image point
  back to the ball about the point,
- the partition of unity over that cover, as
  `EllipticPdes.Extension.nonempty_boundaryPartition`: for a bounded open domain
  with $C^1$ boundary, a `BoundaryPartition` bundles the charts, their centres
  and a smooth partition of unity subordinate to the charts' balls together with
  the domain itself, adding to one on $\overline{\Omega}$. The index is an
  option: the piece indexed by nothing sits inside the domain away from the
  boundary, and the piece indexed by a centre sits in that chart's ball. Mathlib
  proves such partitions for a manifold and a normed space is one over itself,
  so `exists_smooth_partition` reads the smoothness of each piece back as
  $C^\infty$ and nothing downstream of that file meets a manifold,
- the local extension those pieces are summed against, as
  `EllipticPdes.Extension.exists_localExtension` and its form with a constant
  `exists_localExtension_bound`, which is the whole content of
  Guo's second step: near a boundary point the class extends across the
  boundary, to a class with a weak gradient on any ball strictly inside the
  chart's, agreeing with the original on the part of the domain that ball
  meets. The proof composes the chapter. A cutoff between two balls makes the
  class reach the whole region above the chart's graph, the rigid motion takes
  it into the coordinates the graph is written in, the reflection extends it
  across the graph, and the motion takes the result back. Guo runs that step on
  a function smooth up to the boundary and reads the chain rule off it; every
  step here is a weak gradient. The chart asks nothing of the gradient of its
  graph, so the proof runs on the bounded graph `exists_bounded_graph` supplies,
  whose region agrees with the chart's on exactly the ball in play,
- the sum those pieces are glued by, as
  `EllipticPdes.Extension.exists_extension`, which is Guo's third step: on a
  bounded open domain with $C^1$ boundary, a class with a weak gradient on
  $\Omega$ extends to one with a weak gradient on $\mathbb{R}^d$ agreeing with
  it on $\Omega$. Each piece is a local extension cut down by its piece of the
  partition, the cutoff coming after the extension. That order is what makes
  the sum agree: where a piece of the partition is nonzero the point lies in
  that chart's ball, where the local extension agrees with the class, and off
  the ball both sides vanish, so the pieces add to $u$ because the partition
  adds to one,
- the support clause, as `EllipticPdes.Extension.exists_extension_subset`,
  which with the previous item is clauses (i) and (ii) of Guo's Theorem
  III.2.2: any open set the closure of the domain sits in admits a smooth
  cutoff equal to one on that closure, and multiplying by it moves the support
  inside without disturbing the agreement,
- the norm bound, clause (iii), as
  `EllipticPdes.Extension.exists_extension_subset_bound`, which completes
  Theorem III.2.2: one constant, depending on the domain and the exponent and
  quantified before the class, bounds the extension and its gradient in every
  $L^p$ seminorm by the class and its gradient over $\Omega$. The chart, its
  bounded graph, its two cutoffs, the partition of unity and the supremum of
  each piece and of its partials depend on $\Omega$ alone, so
  `exists_localExtension_bound` fixes them before the class appears and
  `exists_extension_bound` sums the local constants over the finitely many
  pieces. The five estimates the chain threads are the cutoff's supremum, the
  rigid motion, the reflection, the shear and the sum over the coordinates the
  motion mixes,
- the operator itself, as `EllipticPdes.Extension.extLinear` and
  `EllipticPdes.Extension.exists_extLinear`, which is §5.4 Theorem 1 of Evans
  as he states it: one $\mathbb{R}$-linear map and one constant serving every
  class. The named forms `localExtension_bound`, `extension_bound` and
  `extension_subset_bound` state the three clauses against
  `EllipticPdes.Extension.extSubsetFun` in place of an existential, and the
  three earlier `exists_` forms are corollaries of them, so nothing downstream
  changed. Linearity is available because the partition, the charts, the
  bounded graphs, the radii and the two cutoffs are all chosen from the domain
  alone, before any class appears: what is left is multiplication by fixed
  functions, precomposition with fixed maps, and a finite sum. The map acts on
  `EllipticPdes.Extension.SobolevPair`, a class paired with a candidate
  gradient, because this development relates the two through `HasWeakGradOn`
  rather than through a bundled Sobolev space; the bound is therefore stated on
  the pair in place of an operator norm, and it is stated at every exponent
  rather than at $2$,
- the operator between the Sobolev spaces themselves, as
  `EllipticPdes.Extension.exists_extW12`, which is Guo's Theorem III.2.2 at
  $p = 2$ as he states it: a bounded linear map from the graph space `W12`
  of the domain, the $H^1(\Omega)$ of this development, to the graph space of
  the whole space, agreeing with the element on the domain in the function and
  the gradient coordinates, with function coordinate vanishing outside the given
  open set, and bounded by a constant times the norm. The map on classes is the
  map on representatives, which descends because it is linear and bounded by the
  seminorms over the domain: two representatives of one class differ by a pair of
  seminorm zero, so their images differ by a function of seminorm zero. That
  closes the difference of space the previous item records,
- global approximation by functions smooth up to the boundary, as
  `EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn`, which is
  §5.3.3 Theorem 3 of Evans at order one: on a bounded domain with $C^1$
  boundary a class with an $L^p$ weak gradient is the $W^{1,p}(\Omega)$ limit
  of smooth compactly supported functions on $\mathbb{R}^d$. Evans shifts the
  class into the domain near each boundary point, mollifies and patches with a
  partition of unity. The extension operator makes the shift unnecessary: the
  mollifications of the extension converge to it in $L^p(\mathbb{R}^d)$
  together with their gradients, and the extension agrees with the class on
  $\Omega$. `exists_smooth_tendsto_of_mem_W12` is the statement at $p = 2$
  for the graph space `W12`, which is density of the smooth functions in
  $H^1(\Omega)$,
- Rellich-Kondrachov on $H^1(\Omega)$, as
  `EllipticPdes.Sobolev.embW12_isCompact`, which is §5.7 Theorem 1 of Evans at
  $p = q = 2$: on a bounded domain with $C^1$ boundary the embedding of the
  graph space `W12` into $L^2(\Omega)$ is compact. `embL2_isCompact` is the
  statement on $H_0^1(\Omega)$, whose proof extends by zero; an element of
  $H^1(\Omega)$ extended by zero jumps at the boundary and loses the
  translation modulus the Fréchet-Kolmogorov criterion asks for. The extension
  operator restores it, `transL2_toLp_sub_le_of_hasWeakGradOn_univ` being the
  modulus of a whole-space class with a weak gradient, and restriction to
  $\Omega$ is Lipschitz,
- Poincaré's inequality with the mean subtracted, as
  `EllipticPdes.Sobolev.poincare_wirtinger`, which is §5.8.1 Theorem 1 of
  Evans at $p = 2$: on a bounded, connected, open domain with $C^1$ boundary
  one constant bounds the $L^2$ distance of every element of $H^1(\Omega)$
  from its mean by the $L^2$ norm of its gradient. The proof is Evans's, by
  contradiction: a sequence of unit $L^2$ norm, zero mean and vanishing
  gradient has an $L^2$-convergent subsequence by Rellich-Kondrachov on
  $H^1(\Omega)$, the graph space is closed so the limit has zero weak
  gradient, and `EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero` makes
  it constant on the connected domain, hence zero by its mean, against its
  norm. That lemma is Evans's Problem 11 of Chapter 5: the mollifications of
  the class have zero classical gradient on any ball whose double lies in the
  domain, so each is constant there and so is their $L^1$ limit, the constants
  spanning a closed line; the constant of a ball is locally constant in its
  centre, hence one value on a preconnected set, and a countable subcover puts
  the class equal to it almost everywhere,
- Poincaré's inequality on a ball, as `EllipticPdes.Sobolev.poincare_ball`,
  which is §5.8.1 Theorem 2 of Evans at $p = 2$: one constant, depending on
  the dimension alone, bounds the $L^2$ distance of a class on any ball from
  its mean over the ball by the radius times the $L^2$ norm of its gradient.
  The unit-ball case is the previous item, and the affine map $y \mapsto ry + x$
  takes it onto the ball: it is a measure-preserving map from the unit ball
  to the ball with Lebesgue measure scaled by $r^{-d}$, so the mean is
  unchanged, the weak gradient picks up the factor $r$, and the seminorm
  factor $r^{-d/2}$ cancels between the two sides,
- the chain rule for weak gradients, as
  `EllipticPdes.Embedding.hasWeakGradOn_comp`, which is Lemma 7.5 of Gilbarg
  and Trudinger: on an open set, a $C^1$ function with bounded derivative,
  composed with a locally integrable class with locally integrable weak
  gradient, has the weak gradient $f'(u)\,\nabla u$. The class is mollified on
  a compact neighbourhood of the support of the test function, the classical
  identity holds for each mollification, and the two sides pass to the limit,
  the gradient side along a subsequence converging almost everywhere. Their
  Lemma 7.6 follows as `EllipticPdes.Embedding.hasWeakGradOn_posPart`, the
  weak gradient of $u^+$ being $\nabla u$ where $u > 0$ and zero elsewhere,
  through the $C^1$ functions $\sqrt{(t^+)^2 + \varepsilon^2} - \varepsilon$,
  with the clauses for $u^-$ and $|u|$ as
  `EllipticPdes.Embedding.hasWeakGradOn_negPart` and
  `EllipticPdes.Embedding.hasWeakGradOn_abs`, and their Lemma 7.7 as
  `EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn`, the weak
  gradient vanishing almost everywhere on every level set,
- the weak maximum principle, as
  `EllipticPdes.Sobolev.weak_maximum_principle`, which is Theorem 8.1 of
  Gilbarg and Trudinger in the transport-free case their proof singles out,
  with nonnegative zeroth-order coefficient and on a bounded open set. The
  boundary inequality $u \le k$ on $\partial\Omega$ is read as they define it,
  as membership of $(u - k)^+$ in $H^1_0(\Omega)$, and the conclusion is
  $u \le k$ almost everywhere for every such $k \ge 0$. The subsolution
  inequality is taken against every nonnegative element of $H^1_0(\Omega)$,
  the form their proof uses; testing against $v = (u - k)^+$, the zeroth-order
  term is nonnegative, the principal term is the energy of $v$ by the chain
  rule for the positive part, ellipticity makes the gradient of $v$ vanish, and
  the Poincaré inequality on $H^1_0$ of the bounded domain makes $v$ vanish.
  The general case with a transport term, which runs through the Sobolev
  inequality and a limit in $k$, is open,
- truncation in $H^1_0$, as
  `EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const`: for $V$ in
  $H^1_0(\Omega)$ and $k \ge 0$, the truncation $(v - k)^+$ with the gradient
  of $v$ on $\{v > k\}$ and zero elsewhere is again in $H^1_0(\Omega)$, which
  is the membership the proof of Theorem 8.1 asserts for its test function. A
  class with $L^2$ weak gradient and compact support in $\Omega$ lies in
  $H^1_0(\Omega)$ by mollification, as
  `EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport`, which is Evans's
  §5.3.1 Theorem 1 applied; the truncations of approximating test functions
  keep compact support because $k \ge 0$, and converge to the truncation of
  the limit, the gradient coordinates along a subsequence converging almost
  everywhere by dominated convergence, the level set $\{v = k\}$ giving
  nothing because the weak gradient vanishes there. With it the principle
  applies to every subsolution in $H^1_0(\Omega)$, as
  `EllipticPdes.Sobolev.weak_maximum_principle_H01`, and their Corollary 8.2,
  the uniqueness of the generalised Dirichlet problem, follows as
  `EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01` by applying the principle
  to the solution and to its negative,
- the weak maximum principle with a transport term, as
  `EllipticPdes.Sobolev.weak_maximum_principle_transport`, which is Theorem
  8.1 of Gilbarg and Trudinger with their coefficients $c^i$ present, in
  dimension at least three. Testing against $v = (u - k)^+$ bounds the energy
  of $v$ by the transport bound times the gradient norm of $v$ times the $L^2$
  norm of $v$ over the set $\Gamma_k$ where $u > k$ and the gradient does not
  vanish; ellipticity, the Sobolev inequality on $H^1_0$ and Hölder's
  inequality then bound the measure of $\Gamma_k$ below by a constant
  independent of $k$ whenever $v \ne 0$. As $k$ increases to the supremum $T$
  of the levels with nonzero truncation, the sets $\Gamma_k$ shrink into
  $\{u \ge T\}$ with nonvanishing gradient, which is null because $\{u > T\}$
  is null by the choice of $T$ and the gradient vanishes almost everywhere on
  $\{u = T\}$; so no level above the boundary value has a nonzero truncation.
  The truncations at every level above the boundary value come from the
  truncation lemma, as `EllipticPdes.Sobolev.exists_truncation_mem_H01`,
- the classical weak maximum principle, as
  `EllipticPdes.Classical.weak_maximum_principle`, which is Evans's §6.4.1
  Theorem 1, Gilbarg and Trudinger's Theorem 3.1 and Guo's Theorem XI.3.7: a
  function $C^2$ on a bounded open set and continuous on its closure, with
  $Lu \le 0$ for the non-divergence-form operator
  $Lu = -a^{ij} u_{x_i x_j} + b^i u_{x_i}$ with symmetric uniformly elliptic
  $a$ and bounded $b$, attains its maximum over the closure on the boundary.
  At an interior local maximum the gradient vanishes and the Hessian is
  negative semidefinite, as `EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax`
  through the one-dimensional second-order test along lines, and the trace
  inequality `EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef`, proved
  through the spectral theorem, makes the principal part nonnegative there; a
  strict subsolution therefore has no interior maximum, and
  $u + \varepsilon e^{\lambda x_1}$ is a strict subsolution for $\lambda$
  large. The supersolution clause is
  `EllipticPdes.Classical.weak_minimum_principle`, and Theorem 2, with
  $c \ge 0$ and the positive part on the boundary, is
  `EllipticPdes.Classical.weak_maximum_principle_of_nonneg`, through Theorem 1
  on the set where $u > 0$,
- Hopf's lemma and the strong maximum principle, as
  `EllipticPdes.Classical.hopf_lemma` and
  `EllipticPdes.Classical.strong_maximum_principle`, which are Evans's §6.4.2
  Lemma and Theorem 3, and Gilbarg and Trudinger's Lemma 3.4 and Theorem 3.5,
  with no zeroth-order term. The barrier
  $e^{-\lambda|x - y|^2} - e^{-\lambda r^2}$ is a subsolution on the annulus
  $r/2 < |x - y| < r$ for $\lambda$ large, vanishes on the outer sphere and is
  positive on the inner one, so $u + \varepsilon v - u(x^0)$ is nonpositive on
  the annulus by the weak maximum principle, and its one-sided derivative at
  $x^0$ along the inward radius is nonpositive, which forces a positive
  outward derivative of $u$. For the strong principle, the set where $u$ is
  below its maximum has a frontier point inside the domain by connectedness;
  the largest ball about a nearby point of that set touches the level set of
  the maximum at a point where Hopf's lemma gives a nonzero gradient, though
  the point is an interior maximum,
- the Gagliardo-Nirenberg-Sobolev inequality on a bounded domain with $C^1$
  boundary, as
  `EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain`, the single rung
  the order-$k$ embedding iterates: a class on $\Omega$ with an $L^p$ weak
  gradient lies in $L^{p'}(\Omega)$ at $1/p' = 1/p - 1/d$, with a constant. On a
  ball the same
  inequality shrinks the ball, the cutoff feeding the whole-space statement
  being one only inside; the extension operator supplies that cutoff once and
  the estimate is on $\Omega$ throughout,
- the Sobolev ladder on that domain, as
  `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`: the rung
  iterated $s$ times with no ball shrinking, so one constant takes a uniform
  $L^{p_0}$ bound on the family to an $L^q$ bound on the member,
- Hölder continuity up to the boundary, as
  `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain`: the
  ladder reaches an exponent above the dimension, the extension puts the member
  and its first derivatives on the whole space, and Morrey on a ball containing
  $\overline{\Omega}$ produces the representative, whose Hölder seminorm on
  $\overline{\Omega}$ one constant bounds by the uniform $L^{p_0}$ bound,
- the representatives of clause (ii) as classical derivatives, as
  `EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain`
  and its two clause forms
  `exists_const_contDiffOn_holderOnWith_domain_ideal` and
  `exists_const_contDiffOn_holderOnWith_domain_free`. One family of
  representatives serves every index at once, so the member is $n$ times
  continuously differentiable on $\Omega$ whenever the supply leaves $n$ orders
  above it, the derivative of one representative being the next. That is what
  $u \in C^{k-1-\lfloor n/p \rfloor, \gamma}(\overline{\Omega})$ asserts,
  where the per-member statement gives only a Hölder representative of each
  derivative separately,
- both clauses of the order-$k$ Sobolev embedding on a bounded $C^1$ domain, as
  `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal`,
  `exists_const_holderOnWith_domain_ideal` and
  `exists_const_holderOnWith_domain_free`. Clause (i) lands on the exponent
  $1/q = 1/p - k/n$ under the strict rung condition $pk < n$; clause (ii) gives
  the Hölder exponent $\lfloor n/p \rfloor - n/p + 1$ when $n/p$ is not an
  integer and any $\gamma \in (0,1)$ when it is, on $\overline{\Omega}$ and
  at every order up to $k - 1 - \lfloor n/p \rfloor$, bounding the supremum and
  the Hölder seminorm together, which is the whole $C^{0,\gamma}$ norm. A member
  of $W^{k,p}(\Omega)$ is read as a family closed under weak differentiation,
  with a depth function in place of
  $D^\alpha u$, which is the vocabulary the interior statements already use,
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

</details>

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
`tsupport φ ⊆ Ω`, so on a set of positive measure
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
