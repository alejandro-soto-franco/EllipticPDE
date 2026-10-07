/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.ClassicalMaximum

/-!
# Hopf's lemma and the strong maximum principle

Hopf's lemma: a `C²` subsolution on a ball, continuous on the closed ball, that is strictly
below its value at a boundary point `x₀` throughout the ball, has positive outward normal
derivative at `x₀`. The barrier `v = exp(-λ|x - y|²) - exp(-λ r²)` is a subsolution on the
annulus `r/2 < |x - y| < r` for `λ` large, vanishes on the outer sphere and is positive on the
inner one, so `u + ε v - u(x₀)` is nonpositive on the boundary of the annulus for `ε` small and,
by the weak maximum principle, on the annulus. Along the inward radius through `x₀` the
function `u + ε v` is therefore at most its value at `x₀`, and its one-sided derivative there,
which is `-∂_ν u(x₀) + ε ∂_ν(-v)(x₀)`, is nonpositive. The normal derivative of `v` is negative,
which gives the strict inequality.

The strong maximum principle: a `C²` subsolution on a connected open set that attains its
maximum at an interior point is constant. If not, the set where the function is below the
maximum is open, nonempty, and has a frontier point inside the set; a small ball about a
nearby point of it, of radius the distance to the level set of the maximum, lies in it and
touches the level set at a point where Hopf's lemma gives a nonzero gradient, though the point
is an interior maximum.

The statements are made on a finite-dimensional real inner product space `E` for the operator
`nondivOperator` of `EllipticPdes.Existence.NondivOperator`; the Euclidean statements with a
coefficient matrix are the wrappers at the end of the file.

## Main declarations

* `EllipticPdes.Classical.nondivOperator.hopf_lemma_ball`: Hopf's lemma on a ball.
* `EllipticPdes.Classical.nondivOperator.hopf_lemma`: Hopf's lemma at a boundary point with the
  interior ball condition.
* `EllipticPdes.Classical.nondivOperator.strong_maximum_principle`: the strong maximum principle.
* `EllipticPdes.Classical.hopf_lemma_ball`, `hopf_lemma`, `strong_maximum_principle`: the
  Euclidean forms.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.4.2 Lemma (Hopf's Lemma, p. 347)
and Theorem 3 (p. 349);
D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
§3.2 Lemma 3.4 (p. 34) and Theorem 3.5 (p. 35).
-/

@[expose] public section

open Set Filter Topology Metric InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

section Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The frontier of an open annulus lies on its two boundary spheres. -/
theorem frontier_ball_sdiff_closedBall_subset (y : E) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    frontier (ball y r \ closedBall y s) ⊆ sphere y r ∪ sphere y s := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans ?_
  rw [frontier_compl, frontier_ball y hr.ne', frontier_closedBall y hs.ne']
  exact union_subset_union inter_subset_left inter_subset_right

/-- A function continuous on a closed ball and at most `c` on the open ball is at most `c` on
the sphere. -/
theorem le_of_forall_ball_le {u : E → ℝ} {y z : E} {r c : ℝ} (hr : 0 < r)
    (huc : ContinuousOn u (closedBall y r)) (h : ∀ x ∈ ball y r, u x ≤ c)
    (hz : dist z y = r) : u z ≤ c :=
  ContinuousWithinAt.closure_le (s := ball y r) (by rw [closure_ball y hr.ne']; exact hz.le)
    ((huc z (mem_closedBall.2 hz.le)).mono ball_subset_closedBall) continuousWithinAt_const h

/-- A point moved from `x₀` towards the centre `y` by the fraction `s ≤ 1` of the radius is at
distance `(1 - s) r` from the centre. -/
theorem dist_add_smul_sub_center {x₀ y : E} {r s : ℝ} (hx₀ : dist x₀ y = r) (hs : s ≤ 1) :
    dist (x₀ + s • (y - x₀)) y = (1 - s) * r := by
  have e : x₀ + s • (y - x₀) - y = (1 - s) • (x₀ - y) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm,
    hx₀]

end Topology

/-- A function continuous on a closed ball and strictly below `u x₀` on the open ball stays a
fixed margin `δ` below `u x₀` on each concentric sphere of smaller radius. -/
theorem exists_gap_on_sphere {E : Type*} [MetricSpace E] [ProperSpace E] {u : E → ℝ} {y x₀ : E}
    {r s : ℝ} (hsr : s < r) (huc : ContinuousOn u (closedBall y r))
    (hlt : ∀ x ∈ ball y r, u x < u x₀) (hne : (sphere y s).Nonempty) :
    ∃ δ > 0, ∀ z ∈ sphere y s, u z ≤ u x₀ - δ := by
  obtain ⟨p, hp, hpmax⟩ := (isCompact_sphere y s).exists_isMaxOn hne
    (huc.mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall hsr.le)))
  have hpb : p ∈ ball y r := by rw [mem_ball, mem_sphere.1 hp]; exact hsr
  exact ⟨u x₀ - u p, sub_pos.2 (hlt p hpb),
    fun z hz => by linarith [(show u z ≤ u p from hpmax hz)]⟩

namespace EllipticPdes.Classical

section Barrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exponential part `exp (-λ ‖x - y‖²)` of the barrier. -/
def barrierExp (lam : ℝ) (y x : E) : ℝ := Real.exp (-lam * ‖x - y‖ ^ 2)

/-- The barrier `exp (-λ ‖x - y‖²) - exp (-λ r²)`. -/
def barrier (lam r : ℝ) (y x : E) : ℝ := barrierExp lam y x - Real.exp (-lam * r ^ 2)

omit [InnerProductSpace ℝ E] in
/-- The exponential part of the barrier is positive. -/
theorem barrierExp_pos (lam : ℝ) (y x : E) : 0 < barrierExp lam y x := Real.exp_pos _

/-- The derivative of the exponential part of the barrier. -/
theorem hasFDerivAt_barrierExp (lam : ℝ) (y x : E) :
    HasFDerivAt (barrierExp lam y)
      (barrierExp lam y x • ((-lam) • (2 • innerSL ℝ (x - y)))) x := by
  have h0 : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const y
  have h1 : HasFDerivAt (fun z : E => ‖z - y‖ ^ 2) (2 • innerSL ℝ (x - y)) x := by
    have := (hasStrictFDerivAt_norm_sq (x - y)).hasFDerivAt.comp x h0
    rwa [ContinuousLinearMap.comp_id] at this
  exact (Real.hasDerivAt_exp (-lam * ‖x - y‖ ^ 2)).comp_hasFDerivAt x (h1.const_mul (-lam))

/-- The barrier is smooth. -/
theorem contDiff_barrier (lam r : ℝ) (y : E) {n : WithTop ℕ∞} : ContDiff ℝ n (barrier lam r y) :=
  (Real.contDiff_exp.comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))).sub
    contDiff_const

/-- The first derivative of the barrier. -/
theorem fderiv_barrier_apply (lam r : ℝ) (y x ξ : E) :
    fderiv ℝ (barrier lam r y) x ξ = -2 * lam * barrierExp lam y x * ⟪x - y, ξ⟫ := by
  have : HasFDerivAt (barrier lam r y)
      (barrierExp lam y x • ((-lam) • (2 • innerSL ℝ (x - y)))) x :=
    (hasFDerivAt_barrierExp lam y x).sub_const _
  simp [this.fderiv, inner_sub_left]
  ring

/-- The second derivative of the barrier. -/
theorem fderiv_fderiv_barrier_apply (lam r : ℝ) (y x ξ η : E) :
    fderiv ℝ (fderiv ℝ (barrier lam r y)) x ξ η
      = barrierExp lam y x * (4 * lam ^ 2 * ⟪x - y, ξ⟫ * ⟪x - y, η⟫ - 2 * lam * ⟪ξ, η⟫) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (barrier lam r y)) x :=
    ((contDiff_barrier lam r y (n := 2)).fderiv_right (m := 1) (by decide)).differentiable
      (by simp) x
  have hfun : (fun z => fderiv ℝ (barrier lam r y) z η)
      = (fun z => -2 * lam * barrierExp lam y z) * (⇑(innerSL ℝ η) ∘ fun z => z - y) :=
    funext fun z => by
      rw [fderiv_barrier_apply]
      simp [real_inner_comm]
  have h0 : HasFDerivAt (fun z : E => z - y) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const y
  have h2 := (((hasFDerivAt_barrierExp lam y x).const_mul (-2 * lam)).mul
    ((innerSL ℝ η).hasFDerivAt.comp x h0))
  have h3 := hd.hasFDerivAt.clm_apply (hasFDerivAt_const η x)
  rw [← hfun] at h2
  have := congrArg (fun L => L ξ) (h3.unique h2)
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply, neg_mul,
    ContinuousLinearMap.comp_id, neg_smul, coe_innerSL_apply, Function.comp_apply, map_sub,
    smul_neg,
    neg_neg, add_apply, neg_apply, smul_apply, smul_eq_mul, sub_apply, nsmul_eq_mul,
    Nat.cast_ofNat] at this
  rw [this]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm ξ η, real_inner_comm x η,
    real_inner_comm y η]
  ring

omit [InnerProductSpace ℝ E] in
/-- The barrier vanishes on the outer sphere. -/
theorem barrier_eq_zero (lam : ℝ) {r : ℝ} {y z : E} (hz : dist z y = r) :
    barrier lam r y z = 0 := by
  simp [barrier, barrierExp, ← dist_eq_norm, hz]

/-- The maximum `exp (-λ (r/2)²) - exp (-λ r²)` of the barrier outside the inner ball. -/
def barrierMax (lam r : ℝ) : ℝ := Real.exp (-lam * (r / 2) ^ 2) - Real.exp (-lam * r ^ 2)

/-- The maximum of the barrier outside the inner ball is positive. -/
theorem barrierMax_pos {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) : 0 < barrierMax lam r := by
  rw [barrierMax, sub_pos]
  refine Real.exp_lt_exp.mpr ?_
  nlinarith [mul_lt_mul_of_pos_left (show (r / 2) ^ 2 < r ^ 2 by nlinarith) hlam]

omit [InnerProductSpace ℝ E] in
/-- Outside the inner ball of radius `r / 2` the barrier is at most `barrierMax`. -/
theorem barrier_le_barrierMax {lam r : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) {y z : E}
    (hz : r / 2 ≤ dist z y) : barrier lam r y z ≤ barrierMax lam r := by
  simp only [barrier, barrierExp, barrierMax, ← dist_eq_norm]
  have h1 : (r / 2) ^ 2 ≤ dist z y ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
  have : -lam * dist z y ^ 2 ≤ -lam * (r / 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam]
  linarith [Real.exp_le_exp.mpr this]

/-- **Radial derivative of the barrier.** At a point of the outer sphere the derivative of the
barrier along the inward radius is `2 λ r² exp (-λ r²)`. -/
theorem fderiv_barrier_radial (lam r : ℝ) {y x₀ : E} (hx₀ : dist x₀ y = r) :
    fderiv ℝ (barrier lam r y) x₀ (y - x₀) = 2 * lam * r ^ 2 * barrierExp lam y x₀ := by
  rw [fderiv_barrier_apply, ← neg_sub x₀ y, inner_neg_right, real_inner_self_eq_norm_sq,
    ← dist_eq_norm, hx₀]
  ring

variable [FiniteDimensional ℝ E]

/-- **Operator on the barrier.** -/
theorem nondivOperator_barrier (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) (lam r : ℝ) (y x : E) :
    nondivOperator A b c (barrier lam r y) x
      = barrierExp lam y x * (2 * lam * LinearMap.trace ℝ E (A x : E →ₗ[ℝ] E)
          - 4 * lam ^ 2 * ⟪x - y, A x (x - y)⟫ - 2 * lam * ⟪b x, x - y⟫)
        + c x * barrier lam r y x := by
  rw [nondivOperator, traceHessian_eq_of_fderiv_fderiv (α := barrierExp lam y x * (4 * lam ^ 2))
    (β := -(barrierExp lam y x * (2 * lam))) (p := x - y) (q := x - y) fun ξ η => by
      rw [fderiv_fderiv_barrier_apply]
      ring, fderiv_barrier_apply, real_inner_comm (b x) (x - y)]
  ring

omit [FiniteDimensional ℝ E] in
/-- A lower bound on a transport term: `-(B (1 + ‖z‖²) / 2) ≤ ⟪b, z⟫` when `‖b‖ ≤ B`. -/
theorem neg_le_inner_of_norm_le {b z : E} {B : ℝ} (hb : ‖b‖ ≤ B) :
    -(B * (1 + ‖z‖ ^ 2) / 2) ≤ ⟪b, z⟫ := by
  have h1 : |⟪b, z⟫| ≤ B * ‖z‖ := (abs_real_inner_le_norm b z).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hb
  nlinarith [neg_abs_le ⟪b, z⟫, sq_nonneg (‖z‖ - 1)]

/-- **Choice of the barrier constant.** For `λ ≥ (S + B (1 + r²) + C) / (θ r²) + 1` and
`r²/4 ≤ q ≤ r²`, `λ (S + B (1 + q)) + C ≤ 4 λ² θ q`. -/
theorem barrier_coefficient_le {S B C θ r q lam : ℝ} (hθ : 0 < θ) (hr : 0 < r) (hS : 0 ≤ S)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hq1 : r ^ 2 / 4 ≤ q) (hq2 : q ≤ r ^ 2)
    (hlam : (S + B * (1 + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam) :
    lam * (S + B * (1 + q)) + C - 4 * lam ^ 2 * θ * q ≤ 0 := by
  have hθr : 0 < θ * r ^ 2 := by positivity
  have hK : 0 ≤ S + B * (1 + r ^ 2) + C := by positivity
  have hlam1 : 1 ≤ lam := by linarith [div_nonneg hK hθr.le]
  have h1 : S + B * (1 + r ^ 2) + C + θ * r ^ 2 ≤ lam * (θ * r ^ 2) := by
    have := mul_le_mul_of_nonneg_right hlam hθr.le
    rwa [add_mul, div_mul_cancel₀ _ hθr.ne', one_mul] at this
  have h2 : lam * θ * r ^ 2 ≤ 4 * lam * θ * q := by nlinarith [mul_pos (by linarith : 0 < lam) hθ]
  have h3 : S + B * (1 + q) + C ≤ 4 * lam * θ * q := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : 0 ≤ lam), mul_le_mul_of_nonneg_left
    (by linarith : 1 ≤ lam) hC]

end Barrier

section Hopf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Barrier as a subsolution on the annulus** for `λ` large: with the bounds on the
coefficients at `x` and `r²/4 ≤ ‖x - y‖² ≤ r²`. -/
theorem nondivOperator_barrier_nonpos {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ}
    {θ T B C r lam : ℝ} (hθ : 0 < θ) (hT : 0 ≤ T) (hB : 0 ≤ B) (hC : 0 ≤ C) {x y : E}
    (hell : θ * ‖x - y‖ ^ 2 ≤ ⟪A x (x - y), x - y⟫)
    (htr : LinearMap.trace ℝ E (A x : E →ₗ[ℝ] E) ≤ T) (hb : ‖b x‖ ≤ B)
    (hcC : c x ≤ C) (hr : 0 < r) (hq1 : r ^ 2 / 4 ≤ ‖x - y‖ ^ 2) (hq2 : ‖x - y‖ ^ 2 ≤ r ^ 2)
    (hlam : (2 * T + B * (1 + r ^ 2) + C) / (θ * r ^ 2) + 1 ≤ lam) :
    nondivOperator A b c (barrier lam r y) x ≤ 0 := by
  rw [nondivOperator_barrier]
  have hw := barrierExp_pos lam y x
  have hbr := barrier_coefficient_le hθ hr (by linarith : 0 ≤ 2 * T) hB hC hq1 hq2 hlam
  have hlam0 : 0 ≤ lam := by
    have : 0 ≤ (2 * T + B * (1 + r ^ 2) + C) / (θ * r ^ 2) := by positivity
    linarith
  have hbar0 : 0 ≤ barrier lam r y x := by
    simp only [barrier, barrierExp, sub_nonneg]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hbar_le : barrier lam r y x ≤ barrierExp lam y x := by
    simp only [barrier, barrierExp]
    linarith [Real.exp_pos (-lam * r ^ 2)]
  have hcv : c x * barrier lam r y x ≤ C * barrierExp lam y x :=
    (mul_le_mul_of_nonneg_right hcC hbar0).trans (mul_le_mul_of_nonneg_left hbar_le hC)
  have hX : 2 * lam * LinearMap.trace ℝ E (A x : E →ₗ[ℝ] E)
      - 4 * lam ^ 2 * ⟪x - y, A x (x - y)⟫ - 2 * lam * ⟪b x, x - y⟫ + C ≤ 0 := by
    rw [real_inner_comm] at hell
    nlinarith [mul_le_mul_of_nonneg_left htr (by linarith : 0 ≤ 2 * lam),
      mul_le_mul_of_nonneg_left hell (by positivity : 0 ≤ 4 * lam ^ 2),
      mul_le_mul_of_nonneg_left (neg_le_inner_of_norm_le (z := x - y) hb)
        (by linarith : 0 ≤ 2 * lam)]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hw.le hX]

omit [FiniteDimensional ℝ E] in
/-- **The perturbed function is below `u x₀` on the boundary of the annulus.** On the outer
sphere `v` vanishes and `u ≤ u x₀`; on the inner sphere `u ≤ u x₀ - δ` and `ε v ≤ δ / 2`. -/
theorem add_mul_barrier_le_of_mem_frontier {u : E → ℝ} {y x₀ z : E} {r lam δ ε : ℝ} (hr : 0 < r)
    (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hεv : ε * barrierMax lam r ≤ δ / 2)
    (huc : ContinuousOn u (closedBall y r)) (hlt : ∀ x ∈ ball y r, u x < u x₀)
    (hgap : ∀ z ∈ sphere y (r / 2), u z ≤ u x₀ - δ)
    (hz : z ∈ frontier (ball y r \ closedBall y (r / 2))) :
    u z + ε * barrier lam r y z ≤ u x₀ := by
  rcases frontier_ball_sdiff_closedBall_subset y hr (half_pos hr) hz with hz | hz
  · rw [barrier_eq_zero lam (mem_sphere.1 hz), mul_zero, add_zero]
    exact le_of_forall_ball_le hr huc (fun x hx => (hlt x hx).le) (mem_sphere.1 hz)
  · have h3 : ε * barrier lam r y z ≤ δ / 2 :=
      (mul_le_mul_of_nonneg_left (barrier_le_barrierMax hlam hr.le (mem_sphere.1 hz).ge) hε).trans
        hεv
    linarith [hgap z hz]

omit [FiniteDimensional ℝ E] in
/-- **From the barrier bound to the normal derivative.** If `u + ε v ≤ u x₀` on the annulus
`r/2 < ‖x - y‖ < r`, with `v` the barrier, and `x₀` is on the outer sphere, a function
differentiable at `x₀` has positive derivative in the outward radial direction. -/
theorem fderiv_pos_of_add_barrier_le {u : E → ℝ} {y x₀ : E} {r lam ε : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hε : 0 < ε) (hx₀ : dist x₀ y = r) (hdiff : DifferentiableAt ℝ u x₀)
    (hbound : ∀ x ∈ ball y r \ closedBall y (r / 2), u x + ε * barrier lam r y x ≤ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have hgd : HasFDerivAt (fun x => u x + ε * barrier lam r y x)
      (fderiv ℝ u x₀ + ε • fderiv ℝ (barrier lam r y) x₀) x₀ :=
    hdiff.hasFDerivAt.add (((contDiff_barrier lam r y (n := 2)).differentiable (by simp)
      x₀).hasFDerivAt.const_mul ε)
  have hmax : IsLocalMaxOn (fun x => u x + ε * barrier lam r y x)
      (insert x₀ (ball y r \ closedBall y (r / 2))) x₀ := by
    refine (isMaxOn_iff.2 fun x hx => ?_).isLocalMaxOn
    rcases hx with rfl | hx
    · exact le_rfl
    · rw [barrier_eq_zero lam hx₀, mul_zero, add_zero]
      exact hbound x hx
  have hseg : (1 / 4 : ℝ) • (y - x₀) ∈
      posTangentConeAt (insert x₀ (ball y r \ closedBall y (r / 2))) x₀ := by
    refine mem_posTangentConeAt_of_segment_subset ?_
    rw [segment_eq_image']
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · simp [← h0]
    · simp only [add_sub_cancel_left, smul_smul]
      refine Or.inr ⟨?_, ?_⟩
      · rw [mem_ball, dist_add_smul_sub_center hx₀ (by nlinarith [ht.2])]
        nlinarith [ht.2]
      · rw [mem_closedBall, not_le, dist_add_smul_sub_center hx₀ (by nlinarith [ht.2])]
        nlinarith [ht.2]
  have hder := hmax.hasFDerivWithinAt_nonpos hgd.hasFDerivWithinAt hseg
  have hfu : fderiv ℝ u x₀ (y - x₀) = -fderiv ℝ u x₀ (x₀ - y) := by rw [← neg_sub, map_neg]
  simp only [add_apply, smul_apply, map_smul, smul_eq_mul, fderiv_barrier_radial lam r hx₀,
    hfu] at hder
  have := barrierExp_pos lam y x₀
  have hpos : 0 < ε * (2 * lam * r ^ 2 * barrierExp lam y x₀) := by positivity
  linarith

end Hopf


namespace nondivOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {θ T B C : ℝ}

/-- **The perturbation by the barrier is below `u x₀` on the annulus.** For a subsolution `u` on
the ball `B(y, r)`, continuous on the closed ball and strictly below `u x₀` throughout the ball,
there are `λ, ε > 0` with `u + ε v ≤ u x₀` on the annulus `r/2 < ‖x - y‖ < r`, where `v` is the
barrier. -/
theorem exists_add_barrier_le {y : E} {r : ℝ} (hr : 0 < r)
    (hA : IsUniformlyElliptic A (ball y r) θ) (hT : ∀ x ∈ ball y r, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ ball y r, ‖b x‖ ≤ B)
    (hc0 : ∀ x ∈ ball y r, 0 ≤ c x) (hcC : ∀ x ∈ ball y r, c x ≤ C) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball y r)) (huc : ContinuousOn u (closedBall y r))
    (hsub : ∀ x ∈ ball y r, nondivOperator A b c u x ≤ 0) {x₀ : E} (hx₀ : dist x₀ y = r)
    (hlt : ∀ x ∈ ball y r, u x < u x₀) (hcu : ∀ x ∈ ball y r, 0 ≤ c x * u x₀) :
    ∃ lam ε : ℝ, 0 < lam ∧ 0 < ε ∧
      ∀ x ∈ ball y r \ closedBall y (r / 2), u x + ε * barrier lam r y x ≤ u x₀ := by
  have hθ := hA.pos
  have hy := mem_ball_self hr (x := y)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hb y hy)
  have hC0 : 0 ≤ C := (hc0 y hy).trans (hcC y hy)
  set T₀ := max T 0
  set R : Set E := ball y r \ closedBall y (r / 2) with hRdef
  have hRo : IsOpen R := isOpen_ball.sdiff isClosed_closedBall
  have hRsub : R ⊆ ball y r := sdiff_subset
  have hx₀0 : x₀ - y ≠ 0 := fun h => by simp [sub_eq_zero.mp h] at hx₀; linarith
  have : Nontrivial E := ⟨⟨x₀ - y, 0, hx₀0⟩⟩
  have hRne : R.Nonempty := ⟨y + (3 * r / 4 / ‖x₀ - y‖) • (x₀ - y), by
    have : ‖(3 * r / 4 / ‖x₀ - y‖) • (x₀ - y)‖ = 3 * r / 4 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity),
        div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx₀0)]
    simp only [hRdef, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, dist_self_add_left, this]
    constructor <;> linarith⟩
  obtain ⟨δ, hδ, hgap⟩ := exists_gap_on_sphere (u := u) (y := y) (x₀ := x₀) (s := r / 2)
    (by linarith) huc hlt (NormedSpace.sphere_nonempty.mpr (by positivity))
  set lam : ℝ := (2 * T₀ + B * (1 + r ^ 2) + C) / (θ * r ^ 2) + 1 with hlam
  have hlam_pos : 0 < lam := by positivity
  set ε : ℝ := δ / (2 * barrierMax lam r) with hε
  have hεpos : 0 < ε := by have := barrierMax_pos hlam_pos hr; positivity
  have hvC := (contDiff_barrier lam r y (n := 2)).contDiffOn (s := R)
  have hgsub : ∀ z ∈ R,
      nondivOperator A b c (fun x => u x + ε * barrier lam r y x - u x₀) z ≤ 0 := by
    intro z hz
    have hzb := hRsub hz
    have hz2 : ‖z - y‖ < r := by simpa [dist_eq_norm] using hz.1
    have hz3 : r / 2 < ‖z - y‖ := by simpa [dist_eq_norm] using hz.2
    have hu2 := hu.contDiffAt (isOpen_ball.mem_nhds hzb)
    have hv2 := (contDiff_barrier lam r y (n := 2)).contDiffAt (x := z)
    rw [nondivOperator_sub_const A b c (hu2.add (contDiffAt_const.mul hv2)),
      nondivOperator_add_smul A b c hu2 hv2]
    have h2 := nondivOperator_barrier_nonpos hθ (le_max_right T 0) hB0 hC0
      (hA.coercive z hzb (z - y)) ((hT z hzb).trans (le_max_left _ _)) (hb z hzb)
      (hcC z hzb) hr (by nlinarith) (by nlinarith [norm_nonneg (z - y)]) le_rfl (A := A)
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hεpos.le h2, hsub z hzb, hcu z hzb]
  have hclR : closure R ⊆ closedBall y r :=
    (closure_mono hRsub).trans (closure_ball y hr.ne').subset
  have hgc : ContinuousOn (fun x => u x + ε * barrier lam r y x - u x₀) (closure R) :=
    ((huc.mono hclR).add (continuousOn_const.mul (contDiff_barrier lam r y
      (n := 2)).continuous.continuousOn)).sub continuousOn_const
  have he : ‖(‖x₀ - y‖⁻¹ : ℝ) • (x₀ - y)‖ = 1 := norm_smul_inv_norm hx₀0
  obtain ⟨z, hzfr, hzmax⟩ := weak_maximum_principle_of_nonneg hRo (isBounded_ball.subset hRsub)
    hRne (hA.mono hRsub) he (fun x hx => (real_inner_le_norm _ _).trans (by
      rw [he, mul_one]; exact hb x (hRsub hx))) (fun x hx => hc0 x (hRsub hx))
    ((hu.mono hRsub).add (contDiffOn_const.mul hvC) |>.sub contDiffOn_const) hgc hgsub
  refine ⟨lam, ε, hlam_pos, hεpos, fun x hx => ?_⟩
  have hεv : ε * barrierMax lam r ≤ δ / 2 := by
    have hM := (barrierMax_pos hlam_pos hr).ne'
    rw [hε]
    field_simp
    exact le_rfl
  have hz' : u z + ε * barrier lam r y z - u x₀ ≤ 0 := by
    linarith [add_mul_barrier_le_of_mem_frontier hr hlam_pos.le hδ.le hεpos.le hεv huc hlt hgap
      hzfr]
  have := hzmax x (subset_closure hx)
  rw [max_eq_right hz'] at this
  linarith


/-- **Hopf's lemma on a ball** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A
subsolution on a ball, continuous on the closed ball, strictly below its value at a point `x₀`
of the sphere throughout the ball, and differentiable at `x₀`, has positive derivative at `x₀`
in the outward radial direction `x₀ - y`. The zeroth-order coefficient is nonnegative and
bounded, and `c u(x₀) ≥ 0`, which covers the clause `c = 0` and the clause `c ≥ 0` with
`u(x₀) ≥ 0`. -/
theorem hopf_lemma_ball {y : E} {r : ℝ} (hr : 0 < r)
    (hA : IsUniformlyElliptic A (ball y r) θ) (hT : ∀ x ∈ ball y r, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ ball y r, ‖b x‖ ≤ B)
    (hc0 : ∀ x ∈ ball y r, 0 ≤ c x) (hcC : ∀ x ∈ ball y r, c x ≤ C) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball y r)) (huc : ContinuousOn u (closedBall y r))
    (hsub : ∀ x ∈ ball y r, nondivOperator A b c u x ≤ 0) {x₀ : E} (hx₀ : dist x₀ y = r)
    (hlt : ∀ x ∈ ball y r, u x < u x₀) (hcu : ∀ x ∈ ball y r, 0 ≤ c x * u x₀)
    (hdiff : DifferentiableAt ℝ u x₀) : 0 < fderiv ℝ u x₀ (x₀ - y) := by
  obtain ⟨lam, ε, hlam, hε, hbound⟩ :=
    exists_add_barrier_le hr hA hT hb hc0 hcC hu huc hsub hx₀ hlt hcu
  exact fderiv_pos_of_add_barrier_le hr hlam hε hx₀ hdiff hbound

/-- **Hopf's lemma** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A subsolution on an
open set, continuous on its closure, strictly below its value at a point `x₀` throughout the
set, and differentiable at `x₀`, has positive derivative at `x₀` in the outward direction of any
ball inside the set whose sphere passes through `x₀`. The zeroth-order coefficient is
nonnegative and bounded with `c u(x₀) ≥ 0`, which covers both clauses of the sources. -/
theorem hopf_lemma {U : Set E} (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x)
    (hcC : ∀ x ∈ U, c x ≤ C) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0)
    {x₀ y : E} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U) (hx₀ : dist x₀ y = r)
    (hlt : ∀ x ∈ U, u x < u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀)
    (hdiff : DifferentiableAt ℝ u x₀) : 0 < fderiv ℝ u x₀ (x₀ - y) :=
  hopf_lemma_ball hr (hA.mono hball) (fun x hx => hT x (hball hx)) (fun x hx => hb x (hball hx))
    (fun x hx => hc0 x (hball hx)) (fun x hx => hcC x (hball hx)) (hu.mono hball)
    (huc.mono (by rw [← closure_ball y hr.ne']; exact closure_mono hball))
    (fun x hx => hsub x (hball hx)) hx₀ (fun x hx => hlt x (hball hx))
    (fun x hx => hcu x (hball hx)) hdiff

/-- **Strong maximum principle** (Evans §6.4.2 Theorem 3, Gilbarg and Trudinger Theorem 3.5).
A subsolution, `C²` on a connected open set, that attains its maximum over the set at an
interior point is constant on the set. The zeroth-order coefficient is nonnegative and bounded
with `c` times the maximum nonnegative, which covers the clause `c = 0` and the clause `c ≥ 0`
with a nonnegative maximum. -/
theorem strong_maximum_principle {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x)
    (hcC : ∀ x ∈ U, c x ≤ C) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hmax : ∀ x ∈ U, u x ≤ u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀) : ∀ x ∈ U, u x = u x₀ := by
  by_contra hne
  simp only [not_forall, exists_prop] at hne
  obtain ⟨x₁, hx₁U, hx₁⟩ := hne
  -- the set where `u` is below the maximum, and a point of the frontier of it inside `U`
  set V : Set E := U ∩ u ⁻¹' Iio (u x₀) with hVdef
  have hVo : IsOpen V := hu.continuousOn.isOpen_inter_preimage hU isOpen_Iio
  have hx₁V : x₁ ∈ V := ⟨hx₁U, lt_of_le_of_ne (hmax x₁ hx₁U) hx₁⟩
  have hex : ∃ z ∈ U, z ∈ closure V ∧ z ∉ V := by
    by_contra hcon
    refine (fun h => lt_irrefl (u x₀) (h hx₀).2 : ¬ U ⊆ V) ?_
    refine hUc.subset_of_closure_inter_subset hVo ⟨x₁, hx₁U, hx₁V⟩ fun z hz => ?_
    by_contra hzV
    exact hcon ⟨z, hz.2, hz.1, hzV⟩
  obtain ⟨z, hzU, hzcl, hzV⟩ := hex
  have hzM : u z = u x₀ := le_antisymm (hmax z hzU) (not_lt.mp fun h => hzV ⟨hzU, h⟩)
  -- a ball in `U` about `z`, a point `y` of `V` near `z`, and the level set near `y`
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.mp hU z hzU
  obtain ⟨y, hyV, hyz⟩ := Metric.mem_closure_iff.mp hzcl (ρ / 2) (by positivity)
  have hcb : closedBall y (ρ / 2) ⊆ U :=
    (closedBall_subset_ball' (by rw [dist_comm]; linarith)).trans hρU
  set K : Set E := closedBall y (ρ / 2) ∩ u ⁻¹' {u x₀} with hKdef
  have hKclosed : IsClosed K := (hu.continuousOn.mono hcb).preimage_isClosed_of_isClosed
    isClosed_closedBall isClosed_singleton
  have hzK : z ∈ K := ⟨mem_closedBall.mpr hyz.le, hzM⟩
  obtain ⟨x₂, hx₂K, hx₂d⟩ := ((isCompact_closedBall y (ρ / 2)).of_isClosed_subset hKclosed
    inter_subset_left).exists_infDist_eq_dist ⟨z, hzK⟩ y
  set r : ℝ := infDist y K with hr
  have hrpos : 0 < r := (infDist_pos_iff_notMem_closure ⟨z, hzK⟩).mp (by
    rw [hKclosed.closure_eq]; exact fun h => hyV.2.ne h.2)
  have hrle : r ≤ ρ / 2 := (infDist_le_dist_of_mem hzK).trans (by rw [dist_comm]; exact hyz.le)
  -- the ball of radius `r` about `y` lies below the maximum and touches the level set at `x₂`
  have hballU : ball y r ⊆ U :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hrle)).trans hcb
  have hballV : ∀ x ∈ ball y r, u x < u x₀ := fun x hx => by
    refine lt_of_le_of_ne (hmax x (hballU hx)) fun h => ?_
    have hxK : x ∈ K := ⟨mem_closedBall.mpr ((mem_ball.mp hx).le.trans hrle), h⟩
    have := infDist_le_dist_of_mem (x := y) hxK
    rw [← hr, dist_comm] at this
    exact absurd (mem_ball.mp hx) (not_lt.mpr this)
  have hx₂dist : dist x₂ y = r := by rw [dist_comm]; exact hx₂d.symm
  have hx₂U : x₂ ∈ U := hcb hx₂K.1
  have hx₂M : u x₂ = u x₀ := hx₂K.2
  have hhopf := hopf_lemma_ball hrpos (hA.mono hballU) (fun x hx => hT x (hballU hx))
    (fun x hx => hb x (hballU hx)) (fun x hx => hc0 x (hballU hx)) (fun x hx => hcC x (hballU hx))
    (hu.mono hballU) (hu.continuousOn.mono ((closedBall_subset_closedBall hrle).trans hcb))
    (fun x hx => hsub x (hballU hx)) hx₂dist (fun x hx => by rw [hx₂M]; exact hballV x hx)
    (fun x hx => by rw [hx₂M]; exact hcu x (hballU hx))
    ((hu.contDiffAt (hU.mem_nhds hx₂U)).differentiableAt (by simp))
  -- but `x₂` is an interior maximum, so the gradient vanishes there
  have hloc : IsLocalMax u x₂ := (show IsMaxOn u U x₂ from fun x hx => by
    rw [hx₂M]; exact hmax x hx).isLocalMax (hU.mem_nhds hx₂U)
  rw [hloc.fderiv_eq_zero] at hhopf
  simp at hhopf

end nondivOperator


/-! ### Euclidean space with a coefficient matrix -/

variable {d : ℕ}

/-- **Hopf's lemma on a ball** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A
subsolution on a ball, continuous on the closed ball, strictly below its value at a point
`x₀` of the sphere throughout the ball, and differentiable at `x₀`, has positive derivative
at `x₀` in the outward radial direction `x₀ - y`. The zeroth-order coefficient is nonnegative
and bounded, and `c u(x₀) ≥ 0`, which covers the clause `c = 0` and the clause `c ≥ 0` with
`u(x₀) ≥ 0`. -/
theorem hopf_lemma_ball (hd : 0 < d) {y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ ball y r, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ ball y r, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ ball y r, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ ball y r, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ ball y r, 0 ≤ c x) (hcC : ∀ x ∈ ball y r, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u (ball y r))
    (huc : ContinuousOn u (closedBall y r))
    (hsub : ∀ x ∈ ball y r, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ ball y r, u x < u x₀)
    (hcu : ∀ x ∈ ball y r, 0 ≤ c x * u x₀) (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have _ := hd
  have hA := isUniformlyElliptic_matrixCLM hθ hsymm hell
  have hT : ∀ x ∈ ball y r, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d))
      (matrixCLM (a x) : _ →ₗ[ℝ] _) ≤ d * A := fun x hx => trace_matrixCLM_le (ha x hx)
  exact nondivOperator.hopf_lemma_ball hr hA hT (fun x hx => norm_toLp_le (hb x hx)) hc0 hcC hu
    huc (fun x hx => by rw [← nondivOp_eq_of_contDiffOn isOpen_ball hu hx]; exact hsub x hx) hx₀
    hlt hcu hdiff

/-- **Hopf's lemma** (Evans §6.4.2 Lemma, Gilbarg and Trudinger Lemma 3.4). A subsolution on
an open set, continuous on its closure, strictly below its value at a point `x₀` throughout the
set, and differentiable at `x₀`, has positive derivative at `x₀` in the outward direction of any
ball inside the set whose sphere passes through `x₀`. The zeroth-order coefficient is
nonnegative and bounded with `c u(x₀) ≥ 0`, which covers both clauses of the sources. -/
theorem hopf_lemma (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀)
    (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have hcl : closedBall y r ⊆ closure U := by
    rw [← closure_ball y hr.ne']
    exact closure_mono hball
  exact hopf_lemma_ball hd hr hθ (fun x hx => hsymm x (hball hx)) (fun x hx => hell x (hball hx))
    (fun x hx => ha x (hball hx)) (fun x hx => hb x (hball hx)) (fun x hx => hc0 x (hball hx))
    (fun x hx => hcC x (hball hx)) (hu.mono hball) (huc.mono hcl)
    (fun x hx => hsub x (hball hx)) hx₀ (fun x hx => hlt x (hball hx))
    (fun x hx => hcu x (hball hx)) hdiff

/-- **Strong maximum principle** (Evans §6.4.2 Theorem 3, Gilbarg and Trudinger Theorem 3.5).
A subsolution, `C²` on a connected open set, that attains its maximum over the set at an
interior point is constant on the set. The zeroth-order coefficient is nonnegative and bounded
with `c` times the maximum nonnegative, which covers the clause `c = 0` and the clause `c ≥ 0`
with a nonnegative maximum. -/
theorem strong_maximum_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hcu : ∀ x ∈ U, 0 ≤ c x * u x₀) :
    ∀ x ∈ U, u x = u x₀ := by
  have _ := hd
  have hA := isUniformlyElliptic_matrixCLM hθ hsymm hell
  exact nondivOperator.strong_maximum_principle hU hUc hA (fun x hx => trace_matrixCLM_le (ha x hx))
    (fun x hx => norm_toLp_le (hb x hx)) hc0 hcC hu
    (fun x hx => by rw [← nondivOp_eq_of_contDiffOn hU hu hx]; exact hsub x hx) hx₀ hmax hcu

/-- **Strong maximum principle with nonnegative zeroth-order coefficient** (Evans §6.4.2
Theorem 3(ii)). With `c ≥ 0`, a subsolution that attains a nonnegative maximum at an interior
point of a connected open set is constant on the set. -/
theorem strong_maximum_principle_of_nonneg (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hu0 : 0 ≤ u x₀) : ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hd hU hUc hθ hsymm hell ha hb hc0 hcC hu hsub hx₀ hmax
    fun x hx => mul_nonneg (hc0 x hx) hu0

end EllipticPdes.Classical
