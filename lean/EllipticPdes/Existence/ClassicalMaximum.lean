/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.NondivOperator
public import EllipticPdes.Sobolev.Basic
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.Connected.Clopen

/-!
# Classical weak maximum principle

The weak maximum principle for a `C²` subsolution of a non-divergence-form elliptic equation
on a bounded open set: the maximum over the closure is attained on the boundary.

The results are stated on a finite-dimensional real inner product space `E` for the operator
`L u = -tr (A D²u) + D u (b) + c u` of `EllipticPdes.Existence.NondivOperator`, with `A x` a
symmetric uniformly elliptic endomorphism field and `b` bounded along a unit vector `e`. At an
interior maximum of a `C²` function the gradient vanishes and the Hessian is negative
semidefinite, so the principal part is nonnegative there; a strict subsolution therefore has no
interior maximum. The general case perturbs by `ε exp(λ ⟪e, x⟫)`, a strict subsolution for `λ`
large, and lets `ε` tend to zero. The Euclidean statements with a coefficient matrix and the
operator `nondivOp` follow from the general ones through the dictionary at the end of the file.

The coefficients are asked to be symmetric, uniformly elliptic and, for the transport term,
bounded on the set; the sources also ask for continuity, which the proof does not use.

## Main declarations

* `EllipticPdes.Classical.weak_maximum_principle`: the weak maximum principle for a
  subsolution with no zeroth-order term.
* `EllipticPdes.Classical.weak_minimum_principle`: the same for a supersolution.
* `EllipticPdes.Classical.weak_maximum_principle_of_nonneg`: the weak maximum principle with
  nonnegative zeroth-order coefficient, through the positive part on the boundary.
* `EllipticPdes.Classical.comparison_principle`, `dirichlet_unique`: the corollaries.
* `EllipticPdes.Classical.nondivOp`: the Euclidean operator with a coefficient matrix, and
  the Euclidean forms of the principles above.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.1 Theorem 1 (p. 343) and
Theorem 2 (p. 344);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.1 Theorem 3.1 (p. 32) and Corollary 3.2 (p. 33);
Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem XI.3.7.
-/

@[expose] public section

open Set Filter Topology InnerProductSpace Metric
open scoped RealInnerProductSpace

noncomputable section

section Topology

/-- A bounded nonempty set in a nontrivial real normed space has nonempty frontier. -/
theorem Bornology.IsBounded.frontier_nonempty {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {U : Set E} (hb : Bornology.IsBounded U) (hne : U.Nonempty) :
    (frontier U).Nonempty := by
  rw [Set.nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff]
  rintro (h | h)
  · exact hne.ne_empty h
  · exact NormedSpace.unbounded_univ ℝ E (h ▸ hb)

/-- A function continuous on the compact closure of a nonempty open set and with no local
maximum in the set attains its maximum over the closure on the frontier. -/
theorem IsOpen.exists_mem_frontier_isMaxOn_of_not_isLocalMax {X : Type*} [TopologicalSpace X]
    {U : Set X} {w : X → ℝ} (hU : IsOpen U) (hcl : IsCompact (closure U)) (hne : U.Nonempty)
    (hw : ContinuousOn w (closure U)) (hno : ∀ z ∈ U, ¬ IsLocalMax w z) :
    ∃ z ∈ frontier U, ∀ x ∈ closure U, w x ≤ w z := by
  obtain ⟨z, hz, hmax⟩ := hcl.exists_isMaxOn (hne.mono subset_closure) hw
  refine ⟨z, ?_, fun x hx => hmax hx⟩
  rw [hU.frontier_eq]
  exact ⟨hz, fun hzU => hno z hzU (hmax.isLocalMax (mem_of_superset (hU.mem_nhds hzU)
    subset_closure))⟩

end Topology

section MatrixTrace

open Matrix

/-- **Trace inequality.** For `A` positive semidefinite and `-H` positive semidefinite,
`∑ᵢⱼ Aᵢⱼ Hᵢⱼ ≤ 0`. Through the spectral theorem `A = U D U*`, the sum is the trace of `A H`,
which is the trace of `D (U* H U)`, a sum of nonnegative eigenvalues times the nonpositive
diagonal entries of `U* H U`. -/
theorem Matrix.PosSemidef.sum_mul_le_zero {n : Type*} [Fintype n]
    {A H : Matrix n n ℝ} (hA : A.PosSemidef) (hH : (-H).PosSemidef) :
    ∑ i, ∑ j, A i j * H i j ≤ 0 := by
  classical
  have hHs : ∀ i j, H i j = H j i := fun i j => by
    have := congrFun (congrFun hH.1 i) j
    simp only [conjTranspose_eq_transpose_of_trivial, transpose_apply, Matrix.neg_apply] at this
    linarith
  have htr : ∑ i, ∑ j, A i j * H i j = trace (A * H) := by
    simp only [trace, diag_apply, mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hHs i j]
  set U : Matrix n n ℝ := (hA.1.eigenvectorUnitary : Matrix n n ℝ)
  have hspec : A = U * diagonal hA.1.eigenvalues * star U := by
    have := hA.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [RCLike.ofReal_real_eq_id, U] using this
  have hconj : (star U * (-H) * U).PosSemidef := by
    have := hH.conjTranspose_mul_mul_same U
    rwa [← star_eq_conjTranspose] at this
  have hdiag : ∀ k, (star U * H * U) k k ≤ 0 := fun k => by
    have h1 := hconj.diag_nonneg (i := k)
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply] at h1
    linarith
  rw [htr, show trace (A * H) = trace (diagonal hA.1.eigenvalues * (star U * H * U)) by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]]
  simp only [trace, diag_apply, diagonal_mul]
  exact Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hA.eigenvalues_nonneg k)
    (hdiag k)

end MatrixTrace

namespace EllipticPdes.Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {U : Set E} {θ B : ℝ}

namespace nondivOperator

/-- **The perturbation is a strict subsolution.** On a set where `A` is uniformly elliptic with
constant `θ` and `⟪b, e⟫ ≤ B` for a unit vector `e`, the function `exp (λ ⟪e, x⟫)` with
`λ = (B + 1) / θ` has `L v < 0` in the absence of a zeroth-order term. -/
theorem expInner_neg (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hB : 0 ≤ B) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) {z : E} (hz : z ∈ U) :
    nondivOperator A b (fun _ => 0) (expInner ((B + 1) / θ) e) z < 0 := by
  rw [nondivOperator_expInner]
  have hθ := hA.pos
  have hlam : (B + 1) / θ * θ = B + 1 := div_mul_cancel₀ _ hθ.ne'
  have hlam0 : 0 < (B + 1) / θ := by positivity
  have h1 : θ ≤ ⟪e, A z e⟫ := by simpa [real_inner_comm] using hA.le_inner_self hz he
  have h2 : ⟪e, b z⟫ ≤ B := by simpa [real_inner_comm] using hb z hz
  refine mul_neg_of_neg_of_pos ?_ (expInner_pos _ _ _)
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ((B + 1) / θ)),
    mul_le_mul_of_nonneg_left h2 hlam0.le]

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1,
Guo Theorem XI.3.7(i)). Let `U` be a bounded open nonempty subset of a finite-dimensional real
inner product space, `L` a non-divergence-form operator with symmetric uniformly elliptic
coefficient, no zeroth-order term and transport `b` with `⟪b, e⟫ ≤ B` along a unit vector `e`, and
`u` a function `C²` on `U` and continuous on its closure with `L u ≤ 0` on `U`. Then the maximum
of `u` over the closure is attained on the boundary. -/
theorem weak_maximum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hsub : ∀ x ∈ U, nondivOperator A b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  have hcl := hUb.isCompact_closure
  set v := expInner ((max B 0 + 1) / θ) e with hv
  have hvd : ContDiff ℝ 2 v := contDiff_expInner _ _
  have hvc : Continuous v := hvd.continuous
  have hbB : ∀ x ∈ U, ⟪b x, e⟫ ≤ max B 0 := fun x hx => (hb x hx).trans (le_max_left _ _)
  -- for `ε > 0` the maximum of `u + ε v` over the closure lies on the frontier
  have key : ∀ ε > 0, ∃ z ∈ frontier U, ∀ x ∈ closure U, u x + ε * v x ≤ u z + ε * v z :=
    fun ε hε => hU.exists_mem_frontier_isMaxOn_of_not_isLocalMax hcl hUne
      (huc.add (continuousOn_const.mul hvc.continuousOn)) fun z hzU hloc => by
        have hu2 := hu.contDiffAt (hU.mem_nhds hzU)
        have hv2 : ContDiffAt ℝ 2 v z := hvd.contDiffAt
        have h1 := le_nondivOperator_of_isLocalMax (c := fun _ => (0 : ℝ)) (b := b)
          (hA.symm z hzU) (hA.psd hzU) (hu2.add (contDiffAt_const.mul hv2)) hloc
        rw [nondivOperator_add_smul A b _ hu2 hv2] at h1
        have h2 := expInner_neg hA he (le_max_right B 0) hbB hzU
        linarith [hsub z hzU, mul_neg_of_pos_of_neg hε h2]
  have hfr : IsCompact (frontier U) :=
    hcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨z₁, hz₁, -⟩ := key 1 one_pos
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn ⟨z₁, hz₁⟩ (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨z₀, -, hz₀⟩ := hcl.exists_isMaxOn ⟨x, hx⟩ hvc.continuousOn
  have hM : 0 < v z₀ := expInner_pos _ _ _
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨z, hzfr, hz⟩ := key (η / v z₀) (div_pos hη hM)
  have h1 := hz x hx
  have h2 : u z ≤ u y := hymax hzfr
  have h3 : v z ≤ v z₀ := hz₀ (frontier_subset_closure hzfr)
  have h4 : η / v z₀ * v z ≤ η := by
    calc η / v z₀ * v z ≤ η / v z₀ * v z₀ := by gcongr
      _ = η := div_mul_cancel₀ _ hM.ne'
  have h5 : 0 < η / v z₀ * v x := mul_pos (div_pos hη hM) (expInner_pos _ _ _)
  linarith

/-- **Weak minimum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)): a supersolution
attains its minimum over the closure on the boundary. -/
theorem weak_minimum_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x := by
  have hneg : ∀ x ∈ U, nondivOperator A b (fun _ => 0) (fun y => -u y) x ≤ 0 := fun x hx => by
    rw [nondivOperator_neg A b _ (hu.contDiffAt (hU.mem_nhds hx))]
    linarith [hsup x hx]
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle hU hUb hUne hA he hb hu.neg huc.neg hneg
  exact ⟨y, hy, fun x hx => by linarith [hmax x hx]⟩

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2, Guo Theorem XI.3.7(ii)). With `c ≥ 0`, a
subsolution is bounded on the closure by the maximum of its positive part over the boundary. -/
theorem weak_maximum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty hUne)
    (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  set K := max (u y) 0 with hK
  set V := U ∩ {z | K < u z} with hV
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hVU : V ⊆ U := inter_subset_left
  have hxV : x ∈ closure V := by
    have hev : ∀ᶠ z in 𝓝[U] x, K < u z :=
      ((huc x hx).mono subset_closure).eventually (lt_mem_nhds hlt)
    rw [mem_closure_iff_nhdsWithin_neBot, hV, nhdsWithin_inter_of_mem' hev]
    exact mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨y', hy'fr, hy'max⟩ := weak_maximum_principle hVo (hUb.subset hVU)
    (closure_nonempty_iff.mp ⟨x, hxV⟩) (hA.mono hVU)
    he (fun z hz => hb z (hVU hz)) (hu.mono hVU) (huc.mono (closure_mono hVU)) fun z hz => by
      have := nondivOperator_congr_zeroth A b c (fun _ => 0) u z
      have h3 : 0 ≤ c z * u z := mul_nonneg (hc z (hVU hz)) ((le_max_right _ _).trans hz.2.le)
      linarith [hsub z (hVU hz), nondivOperator_congr_zeroth A b (fun _ => 0) c u z]
  have hy'cl := (hVo.frontier_eq ▸ hy'fr : y' ∈ closure V \ V)
  have hy'K : u y' ≤ K := by
    by_cases hy'U : y' ∈ U
    · exact not_lt.mp fun h => hy'cl.2 ⟨hy'U, h⟩
    · refine (hymax ?_).trans (le_max_left _ _)
      rw [hU.frontier_eq]
      exact ⟨closure_mono hVU hy'cl.1, hy'U⟩
  linarith [hy'max x hxV]

/-- **Strict maximum principle** (Guo Theorem XI.3.5). A strict subsolution, meaning `L u < 0` at
a point, has no local maximum there whenever `c u ≥ 0` at the point. -/
theorem not_isLocalMax_of_neg {x₀ : E} (hsymm : (A x₀ : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ ξ, 0 ≤ ⟪A x₀ ξ, ξ⟫) {u : E → ℝ} (hu : ContDiffAt ℝ 2 u x₀)
    (hcu : 0 ≤ c x₀ * u x₀) (hstrict : nondivOperator A b c u x₀ < 0) : ¬ IsLocalMax u x₀ :=
  fun hmax => absurd (le_nondivOperator_of_isLocalMax (b := b) (c := c) hsymm hpsd hu hmax)
    (not_le.mpr (hstrict.trans_le hcu))

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3, Guo Corollary XI.3.11). With
`c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on the closure. -/
theorem comparison_principle (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc
    (hu.add (contDiffOn_const.mul hv)) (huc.add (continuousOn_const.mul hvc)) (u := fun z =>
      u z + (-1) * v z) fun x hx => by
    rw [nondivOperator_add_smul A b c (hu.contDiffAt (hU.mem_nhds hx))
      (hv.contDiffAt (hU.mem_nhds hx))]
    linarith [hL x hx]
  intro x hx
  have h1 := hmax x hx
  rw [max_eq_right (by linarith [hbd y hy])] at h1
  linarith

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause). With
`c ≥ 0`, a solution of `L u = 0` on a bounded open set is bounded in absolute value on the
closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_eq_zero (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOperator A b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty hUne)
    (huc.mono frontier_subset_closure).abs
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu huc
    fun z hz => (hsol z hz).le
  obtain ⟨y₂, hy₂, h₂⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu.neg huc.neg
    fun z hz => by rw [nondivOperator_neg A b c (hu.contDiffAt (hU.mem_nhds hz)), hsol z hz,
      neg_zero]
  have hx₁ : u x ≤ |u y| := (h₁ x hx).trans (max_le ((le_abs_self _).trans (hymax hy₁))
    (abs_nonneg _))
  have hx₂ : -u x ≤ |u y| := (h₂ x hx).trans (max_le ((neg_le_abs _).trans (hymax hy₂))
    (abs_nonneg _))
  exact abs_le.mpr ⟨by linarith, hx₁⟩

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)). With `c ≥ 0`, a supersolution is bounded below on the closure by the minimum of
its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOperator A b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x := by
  obtain ⟨y, hy, hmax⟩ := weak_maximum_principle_of_nonneg hU hUb hUne hA he hb hc hu.neg huc.neg
    fun x hx => by
      rw [nondivOperator_neg A b c (hu.contDiffAt (hU.mem_nhds hx))]
      linarith [hsup x hx]
  refine ⟨y, hy, fun x hx => ?_⟩
  have h := hmax x hx
  have e : min (u y) 0 = -max (-u y) 0 := by rw [← min_neg_neg, neg_neg, neg_zero]
  rw [e]
  linarith

/-- **Uniqueness for the Dirichlet problem** (Guo Corollary XI.3.9). With `c ≥ 0`, two functions
with the same image under `L` on the set and the same boundary values agree on the closure. -/
theorem dirichlet_unique (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B)
    (hc : ∀ x ∈ U, 0 ≤ c x) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x = nondivOperator A b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := fun x hx =>
  le_antisymm
    (comparison_principle hU hUb hUne hA he hb hc hu hv huc hvc (fun x hx => (hL x hx).le)
      (fun x hx => (hbd x hx).le) x hx)
    (comparison_principle hU hUb hUne hA he hb hc hv hu hvc huc (fun x hx => (hL x hx).ge)
      (fun x hx => (hbd x hx).ge) x hx)

end nondivOperator

/-- **Trace inequality** for matrices (`Fin d`-indexed form). -/
theorem sum_mul_nonpos_of_posSemidef {d : ℕ} {A H : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) (hH : (-H).PosSemidef) : ∑ i, ∑ j, A i j * H i j ≤ 0 :=
  hA.sum_mul_le_zero hH

/-! ### Euclidean space with a coefficient matrix -/

open EllipticPdes.Sobolev (partialD partialD_apply)

variable {d : ℕ}

/-- **Hessian at an interior local maximum** on Euclidean space. -/
theorem sndFDeriv_nonpos_of_isLocalMax {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hu : ContDiffAt ℝ 2 u x₀) (hmax : IsLocalMax u x₀)
    (ξ : EuclideanSpace ℝ (Fin d)) : fderiv ℝ (fderiv ℝ u) x₀ ξ ξ ≤ 0 :=
  hmax.fderiv_fderiv_nonpos hu ξ

/-- **Non-divergence-form operator** `L u = -∑ aᵢⱼ ∂ᵢ∂ⱼ u + ∑ bᵢ ∂ᵢ u + c u` with a coefficient
matrix `a x` and transport `b x` on Euclidean space. -/
def nondivOp (a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ)
    (b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ) (c : EuclideanSpace ℝ (Fin d) → ℝ)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(∑ i, ∑ j, a x i j * partialD i (partialD j u) x) + ∑ i, b x i * partialD i u x + c x * u x

/-- The endomorphism of Euclidean space with the matrix `M`. -/
abbrev matrixCLM (M : Fin d → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (Matrix.of M)

/-- The coordinates of `matrixCLM M ξ`. -/
theorem matrixCLM_apply (M : Fin d → Fin d → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    matrixCLM M ξ i = ∑ j, M i j * ξ j := rfl

/-- The quadratic form of `matrixCLM M` is the quadratic form of `M`. -/
theorem inner_matrixCLM (M : Fin d → Fin d → ℝ) (ξ : EuclideanSpace ℝ (Fin d)) :
    ⟪matrixCLM M ξ, ξ⟫ = ∑ i, ∑ j, M i j * ξ i * ξ j := by
  simp only [PiLp.inner_apply, matrixCLM_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A symmetric matrix gives a symmetric endomorphism. -/
theorem isSymmetric_matrixCLM {M : Fin d → Fin d → ℝ} (h : ∀ i j, M i j = M j i) :
    ((matrixCLM M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).IsSymmetric := fun ξ η => by
  simp only [ContinuousLinearMap.coe_coe, PiLp.inner_apply, matrixCLM_apply, RCLike.inner_apply,
    conj_trivial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h i j]
  ring

/-- The trace of `matrixCLM M` is the trace of `M`. -/
theorem trace_matrixCLM (M : Fin d → Fin d → ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (matrixCLM M : _ →ₗ[ℝ] _) = ∑ i, M i i := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [EuclideanSpace.inner_single_left, matrixCLM_apply, PiLp.single_apply]

/-- `matrixCLM M` maps the `i`-th basis vector to the `i`-th column. -/
theorem matrixCLM_single (M : Fin d → Fin d → ℝ) (i : Fin d) :
    matrixCLM M (EuclideanSpace.single i 1) = ∑ j, M j i • EuclideanSpace.single j 1 := by
  ext k
  simp [matrixCLM_apply, Finset.sum_apply, PiLp.single_apply, Pi.single_apply]

/-- `tr (matrixCLM M D²u(x)) = ∑ᵢⱼ Mᵢⱼ D²u(x)(eᵢ, eⱼ)`. -/
theorem traceHessian_matrixCLM (M : Fin d → Fin d → ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    traceHessian (matrixCLM M) u x
      = ∑ i, ∑ j, M i j * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  rw [traceHessian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ), Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [EuclideanSpace.basisFun_apply, matrixCLM_single, map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]

/-- The second partial derivatives are the entries of the Hessian. -/
theorem partialD_partialD_eq {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : Fin d) :
    partialD i (partialD j u) x
      = fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have : partialD j u = fun y => fderiv ℝ u y (EuclideanSpace.single j 1) := rfl
  rw [partialD_apply, this, fderiv_clm_apply hu (differentiableAt_const _)]
  simp

/-- The first partials are the coordinates of the derivative. -/
theorem fderiv_toLp_eq_sum (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    (v : Fin d → ℝ) : fderiv ℝ u x (WithLp.toLp 2 v) = ∑ i, v i * partialD i u x := by
  have : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = ∑ i, v i • EuclideanSpace.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, map_sum]
  simp [partialD_apply]

/-- **The Euclidean operator is the coordinate-free one** for a function `C²` at the point. -/
theorem nondivOp_eq {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hu : ContDiffAt ℝ 2 u x) :
    nondivOp a b c u x = nondivOperator (fun y => matrixCLM (a y))
      (fun y => WithLp.toLp 2 (b y)) c u x := by
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by decide)).differentiableAt (by simp)
  simp only [nondivOp, nondivOperator, traceHessian_matrixCLM, fderiv_toLp_eq_sum,
    partialD_partialD_eq hd2]

/-- Pointwise form of `nondivOp_eq` on an open set where `u` is `C²`. -/
theorem nondivOp_eq_of_contDiffOn {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    nondivOp a b c u x = nondivOperator (fun y => matrixCLM (a y))
      (fun y => WithLp.toLp 2 (b y)) c u x :=
  nondivOp_eq (hu.contDiffAt (hU.mem_nhds hx))

/-- The Euclidean ellipticity hypotheses make the matrix an elliptic endomorphism field. -/
theorem isUniformlyElliptic_matrixCLM {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) :
    IsUniformlyElliptic (fun x => matrixCLM (a x)) U θ :=
  ⟨hθ, fun x hx => isSymmetric_matrixCLM (hsymm x hx), fun x hx ξ => by
    rw [inner_matrixCLM, EuclideanSpace.norm_sq_eq]
    simpa using hell x hx (WithLp.ofLp ξ)⟩

/-- The coordinate bound `|bᵢ| ≤ B` gives `⟪b, e⟫ ≤ B` for the first basis vector `e`. -/
theorem exists_unit_inner_le (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {B : ℝ} (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
      ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)), e⟫ ≤ B :=
  ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by simp, fun x hx => by
    rw [EuclideanSpace.inner_single_right]
    simpa using (abs_le.mp (hb x hx ⟨0, hd⟩)).2⟩

/-- The Euclidean hypotheses on the coefficients give the coordinate-free ones: the matrix is
uniformly elliptic as an endomorphism field, and `⟪b, e⟫ ≤ B` for the first basis vector. -/
theorem euclid_data (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {θ B : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) :
    IsUniformlyElliptic (fun x => matrixCLM (a x)) U θ ∧
      ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
        ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)), e⟫ ≤ B :=
  ⟨isUniformlyElliptic_matrixCLM hθ hsymm hell, exists_unit_inner_le hd hb⟩

/-- The trace of the matrix endomorphism is at most `d` times a bound on the entries. -/
theorem trace_matrixCLM_le {M : Fin d → Fin d → ℝ} {A : ℝ} (hM : ∀ i j, |M i j| ≤ A) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (matrixCLM M : _ →ₗ[ℝ] _) ≤ d * A := by
  rw [trace_matrixCLM]
  calc ∑ i, M i i ≤ ∑ _i : Fin d, A := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hM i i)
    _ = d * A := by simp

/-- The Euclidean norm of a vector is at most `d` times a bound on its coordinates. -/
theorem norm_toLp_le {v : Fin d → ℝ} {B : ℝ} (hv : ∀ i, |v i| ≤ B) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ ≤ d * B := by
  have : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) = ∑ i, v i • EuclideanSpace.single i 1 := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖v i • (EuclideanSpace.single i (1 : ℝ))‖ ≤ ∑ _i : Fin d, B :=
        Finset.sum_le_sum fun i _ => by simpa [norm_smul] using hv i
    _ = d * B := by simp

/-- **Weak maximum principle** (Evans §6.4.1 Theorem 1(i), Gilbarg and Trudinger Theorem 3.1,
Guo Theorem XI.3.7(i)). Let `U` be a bounded open nonempty set, `L` a non-divergence-form
operator with symmetric uniformly elliptic coefficients, bounded transport coefficients and no
zeroth-order term, and `u` a function `C²` on `U` and continuous on its closure with `L u ≤ 0`
on `U`. Then the maximum of `u` over the closure is attained on the boundary. -/
theorem weak_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b (fun _ => 0) u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ u y := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_maximum_principle hU hUb hUne hA he hb' hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsub x hx

/-- **Weak minimum principle for supersolutions** (Evans §6.4.1 Theorem 1(ii)). A
supersolution attains its minimum over the closure on the boundary. -/
theorem weak_minimum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b (fun _ => 0) u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u y ≤ u x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_minimum_principle hU hUb hUne hA he hb' hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsup x hx

/-- **Weak maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(i), Gilbarg and Trudinger Corollary 3.2, Guo Theorem XI.3.7(ii)). With `c ≥ 0`, a
subsolution is bounded on the closure by the maximum of its positive part over the boundary. -/
theorem weak_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, u x ≤ max (u y) 0 := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_maximum_principle_of_nonneg hU hUb hUne hA he hb' hc hu huc
    fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx]
      exact hsub x hx

/-- **Weak minimum principle with nonnegative zeroth-order coefficient** (Evans §6.4.1
Theorem 2(ii)). With `c ≥ 0`, a supersolution is bounded below on the closure by the minimum
of its negative part over the boundary. -/
theorem weak_minimum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsup : ∀ x ∈ U, 0 ≤ nondivOp a b c u x) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, min (u y) 0 ≤ u x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.weak_minimum_principle_of_nonneg hU hUb hUne hA he hb' hc hu huc
    fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx]
      exact hsup x hx

/-- **Strict maximum principle** (Guo Theorem XI.3.5). A strict subsolution, meaning
`L u < 0` at a point, has no local maximum at that point whenever `c u ≥ 0` there: in
particular when `c = 0`, when `c ≥ 0` and the maximum is nonnegative, and when the maximum is
zero. -/
theorem not_isLocalMax_of_nondivOp_neg {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin d)} (hsymm : ∀ i j, a x₀ i j = a x₀ j i)
    (hpsd : ∀ ξ : Fin d → ℝ, 0 ≤ ∑ i, ∑ j, a x₀ i j * ξ i * ξ j)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffAt ℝ 2 u x₀) (hcu : 0 ≤ c x₀ * u x₀)
    (hstrict : nondivOp a b c u x₀ < 0) : ¬ IsLocalMax u x₀ :=
  nondivOperator.not_isLocalMax_of_neg (A := fun y => matrixCLM (a y))
    (b := fun y => WithLp.toLp 2 (b y)) (c := c) (isSymmetric_matrixCLM hsymm)
    (fun ξ => by simpa [inner_matrixCLM] using hpsd (WithLp.ofLp ξ)) hu hcu
    (by rwa [nondivOp_eq hu] at hstrict)

/-- **Comparison principle** (Gilbarg and Trudinger Theorem 3.3, Guo Corollary XI.3.11). With
`c ≥ 0`, if `L u ≤ L v` on the set and `u ≤ v` on the boundary, then `u ≤ v` on the closure. -/
theorem comparison_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x ≤ v x) : ∀ x ∈ closure U, u x ≤ v x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.comparison_principle hU hUb hUne hA he hb' hc hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hbd

/-- **Bound by the boundary values** (Gilbarg and Trudinger Corollary 3.2, second clause). With
`c ≥ 0`, a solution of `L u = 0` on a bounded open set is bounded in absolute value on the
closure by the maximum of `|u|` over the boundary. -/
theorem abs_le_of_nondivOp_eq_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOp a b c u x = 0) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U, |u x| ≤ |u y| := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.abs_le_of_eq_zero hU hUb hUne hA he hb' hc hu huc fun x hx => by
    rw [← nondivOp_eq_of_contDiffOn hU hu hx]
    exact hsol x hx

/-- **Uniqueness for the Dirichlet problem** (Guo Corollary XI.3.9). With `c ≥ 0`, two
functions with the same image under `L` on the set and the same boundary values agree on the
closure. -/
theorem dirichlet_unique (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hbd : ∀ x ∈ frontier U, u x = v x) : ∀ x ∈ closure U, u x = v x := by
  obtain ⟨hA, e, he, hb'⟩ := euclid_data hd hθ hsymm hell hb
  exact nondivOperator.dirichlet_unique hU hUb hUne hA he hb' hc hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hbd

end EllipticPdes.Classical
