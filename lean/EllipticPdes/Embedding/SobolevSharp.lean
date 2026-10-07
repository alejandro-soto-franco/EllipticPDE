/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.Dilation
public import EllipticPdes.Embedding.H01Sobolev
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Sharpness of the Sobolev embedding

The embedding of `H₀¹(Ω)` into `L^q(Ω)` is compact below the Sobolev conjugate and at the
conjugate itself is bounded. It is not compact there, and the obstruction is scaling: the
dilates of a fixed test function, renormalised to keep their `L^{2⋆}` norm, keep their gradient
norm as well and lose their `L²` norm.

Writing `φ_λ(x) = φ(x/λ)` and `v_λ = λ^{1 - d/2} φ_λ`, the three identities are

`‖v_λ‖_{L^{2⋆}} = ‖φ‖_{L^{2⋆}}`, `‖v_λ‖_{L²} = λ‖φ‖_{L²}`, `‖∂ᵢ v_λ‖_{L²} = ‖∂ᵢφ‖_{L²}`,

and the reason is `d/2⋆ = d/2 - 1`, the Sobolev relation itself. A family bounded in
`H₀¹(Ω)` whose images keep a fixed positive `L^{2⋆}` norm and tend to zero in `L²` has no
`L^{2⋆}`-convergent subsequence.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_dilate`: the `Lᵖ` seminorm of a dilate on the unit ball.
* `EllipticPdes.Embedding.eLpNorm_partialD_dilate`: the same for its partial derivatives.
* `EllipticPdes.Embedding.isTestFn_dilate`: a dilate of a test function is a test function.

## References

Y. Guo, *Partial Differential Equations*, Example IV.2.11.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis

variable {d : ℕ}

/-- The dilate `x ↦ φ(x/lam)` of a test function supported in the closed unit ball is a test
function on the unit ball, for `0 < lam ≤ 1/2`. -/
theorem isTestFn_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) φ)
    (hsupp : tsupport φ ⊆ closedBall 0 1) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1 / 2) :
    IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (fun x => φ (lam⁻¹ • x)) := by
  have hsub : tsupport (fun x => φ (lam⁻¹ • x)) ⊆ closedBall 0 lam := by
    have := tsupport_comp_smul_subset_closedBall (f := φ) (r := lam⁻¹) (by positivity) hsupp
    rwa [inv_inv] at this
  refine ⟨h.1.comp (contDiff_const_smul _), ?_, hsub.trans ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) lam)
      ((subset_tsupport _).trans hsub)
  · intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_ball, dist_zero_right]
    linarith

/-- **`Lᵖ` seminorm of a dilate**, over the unit ball, where both sides see the whole space
since the supports lie inside. -/
theorem eLpNorm_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : Measurable φ)
    {lam : ℝ} (hlam0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (fun x => φ (lam⁻¹ • x)) p volume
      = ENNReal.ofReal (lam ^ d) ^ (1 / p.toReal) * eLpNorm φ p volume := by
  rw [eLpNorm_comp_smul hφ (by positivity) hp0 hpt]
  congr 2
  rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]

/-- **Partial derivatives of a dilate**, in `Lᵖ`. -/
theorem eLpNorm_partialD_dilate {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (i : Fin d) (hmeas : Measurable (partialD i φ))
    {lam : ℝ} (hlam0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (partialD i (fun x => φ (lam⁻¹ • x))) p volume
      = ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (lam ^ d) ^ (1 / p.toReal)
          * eLpNorm (partialD i φ) p volume) := by
  rw [partialD_comp_smul (hφ.differentiable one_ne_zero) _ i]
  rw [show (fun x => lam⁻¹ * partialD i φ (lam⁻¹ • x))
      = lam⁻¹ • (fun y => partialD i φ (lam⁻¹ • y)) from rfl,
    eLpNorm_const_smul, eLpNorm_comp_smul hmeas (by positivity) hp0 hpt]
  congr 2
  · simp [Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hlam0)]
  · rw [inv_pow, inv_inv, abs_of_nonneg (by positivity)]


/-! ### The test function the argument dilates -/

/-- A bump on the unit ball: one on `closedBall 0 (1/4)` and supported in `closedBall 0 (1/2)`. -/
def sharpBump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- `sharpBump d` has topological support the closed ball of radius `1 / 2` about the origin. -/
@[simp] lemma tsupport_sharpBump :
    tsupport (⇑(sharpBump d)) = closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) :=
  (sharpBump d).tsupport_eq

/-- `sharpBump d` has topological support inside the closed unit ball. -/
lemma tsupport_sharpBump_subset :
    tsupport (⇑(sharpBump d)) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  rw [tsupport_sharpBump]
  exact closedBall_subset_closedBall (by norm_num)

/-- `sharpBump d` is a test function on the open unit ball. -/
lemma isTestFn_sharpBump : IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (⇑(sharpBump d)) := by
  refine ⟨(sharpBump d).contDiff, (sharpBump d).hasCompactSupport, ?_⟩
  rw [tsupport_sharpBump]
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  linarith

/-- `sharpBump d` takes the value `1` at the origin. -/
lemma sharpBump_zero : (sharpBump d) 0 = 1 :=
  (sharpBump d).one_of_mem_closedBall (mem_closedBall_self (sharpBump d).rIn_pos.le)

/-- The bump has positive `Lᵖ` seminorm, being continuous and nonzero at the origin. -/
lemma eLpNorm_sharpBump_ne_zero {p : ℝ≥0∞} (hp0 : p ≠ 0) :
    eLpNorm (⇑(sharpBump d)) p volume ≠ 0 := by
  rw [Ne, eLpNorm_eq_zero_iff hp0]
  intro hae
  have hzero : (⇑(sharpBump d) : EuclideanSpace ℝ (Fin d) → ℝ) = 0 :=
    (sharpBump d).continuous.ae_eq_iff_eq volume continuous_const |>.mp hae
  have := sharpBump_zero (d := d)
  rw [hzero] at this
  simp at this

/-! ### The graph coordinates of a test function -/

variable {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- The function coordinate of a test graph, in `Lᵖ` over the whole space. -/
lemma eLpNorm_testGraph_zero_eq (hΩm : MeasurableSet Ω) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω ψ) (p : ℝ≥0∞) :
    eLpNorm (h.testGraph 0 : L2D Ω) p (volume.restrict Ω) = eLpNorm ψ p volume := by
  rw [eLpNorm_testGraph_zero p h, eLpNorm_restrict_eq_of_tsupport_subset hΩm h.2.2 p]

/-- A gradient coordinate of a test graph, in `Lᵖ` over the whole space. -/
lemma eLpNorm_testGraph_succ_eq (hΩm : MeasurableSet Ω) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω ψ) (p : ℝ≥0∞) (i : Fin d) :
    eLpNorm (h.testGraph i.succ : L2D Ω) p (volume.restrict Ω)
      = eLpNorm (partialD i ψ) p volume := by
  rw [IsTestFn.testGraph_succ, IsTestFn.partialCls,
    eLpNorm_congr_ae (h.memLp_partialD i).coeFn_toLp,
    eLpNorm_restrict_eq_of_tsupport_subset hΩm ((tsupport_partialD_subset i ψ).trans h.2.2) p]


/-! ### The renormalised dilates -/

/-- `lam^{1 - d/2} φ(·/lam)`, the dilate renormalised to keep its `L^{2⋆}` norm. -/
def sharpFamily (d : ℕ) (lam : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (lam ^ (1 - (d : ℝ) / 2)) • fun x => (sharpBump d) (lam⁻¹ • x)

/-- `sharpFamily d lam` is a test function on the open unit ball for `0 < lam ≤ 1 / 2`. -/
lemma isTestFn_sharpFamily {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    IsTestFn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (sharpFamily d lam) :=
  (isTestFn_dilate isTestFn_sharpBump tsupport_sharpBump_subset h0 h1).const_smul _

private lemma rpow_pow_mul {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (t : ℝ) :
    (lam ^ n) ^ t = lam ^ ((n : ℝ) * t) := by
  rw [← Real.rpow_natCast lam n, ← Real.rpow_mul hlam.le]

/-- The `Lᵖ` seminorm of a renormalised dilate, with the two powers of `lam` collected. -/
lemma eLpNorm_sharpFamily {lam : ℝ} (h0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (sharpFamily d lam) p volume
      = ENNReal.ofReal (lam ^ (1 - (d : ℝ) / 2 + (d : ℝ) * (1 / p.toReal)))
        * eLpNorm (⇑(sharpBump d)) p volume := by
  rw [sharpFamily, eLpNorm_const_smul,
    eLpNorm_dilate (sharpBump d).continuous.measurable h0 hp0 hpt,
    ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos h0 _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr ENNReal.toReal_nonneg),
    rpow_pow_mul h0, ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos h0 _)),
    ← Real.rpow_add h0]

/-- The same for a gradient coordinate, which picks up one further power of the dilation. -/
lemma eLpNorm_partialD_sharpFamily {lam : ℝ} (h0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hpt : p ≠ ∞) (i : Fin d) :
    eLpNorm (partialD i (sharpFamily d lam)) p volume
      = ENNReal.ofReal (lam ^ (1 - (d : ℝ) / 2 - 1 + (d : ℝ) * (1 / p.toReal)))
        * eLpNorm (partialD i (⇑(sharpBump d))) p volume := by
  have hdiff : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin d) => (sharpBump d) (lam⁻¹ • x)) :=
    ((sharpBump d).contDiff (n := 1)).differentiable (by norm_num) |>.comp
      ((differentiable_id).const_smul lam⁻¹)
  have hmeas : Measurable (partialD i (⇑(sharpBump d))) :=
    ((isTestFn_sharpBump (d := d)).continuous_partialD i).measurable
  rw [sharpFamily, partialD_const_smul hdiff _ i, eLpNorm_const_smul,
    eLpNorm_partialD_dilate ((sharpBump d).contDiff (n := 1)) i hmeas h0 hp0 hpt,
    ← mul_assoc, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos h0 _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr ENNReal.toReal_nonneg),
    rpow_pow_mul h0, ← Real.rpow_neg_one lam,
    ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos h0 _)),
    ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_add h0, ← Real.rpow_add h0]
  ring_nf


/-! ### The family in `H₀¹` of the unit ball -/

/-- The renormalised dilate, as an element of `H₀¹` of the unit ball. -/
def sharpElt (d : ℕ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
  ⟨(isTestFn_sharpFamily h0 h1).testGraph,
    (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨sharpFamily d lam, isTestFn_sharpFamily h0 h1, rfl⟩)⟩

variable {lam : ℝ}

/-- The function coordinate of `sharpElt d h0 h1` has the same `eLpNorm` on the unit ball as
`sharpFamily d lam` has on the whole space. -/
lemma eLpNorm_sharpElt_zero (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) {p : ℝ≥0∞} :
    eLpNorm (((sharpElt d h0 h1 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
        H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 0) p
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (sharpFamily d lam) p volume :=
  eLpNorm_testGraph_zero_eq measurableSet_ball (isTestFn_sharpFamily h0 h1) p

/-- The `i`-th gradient coordinate of `sharpElt d h0 h1` has the same `eLpNorm` on the unit ball as
`partialD i (sharpFamily d lam)` has on the whole space. -/
lemma eLpNorm_sharpElt_succ (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) {p : ℝ≥0∞} (i : Fin d) :
    eLpNorm (((sharpElt d h0 h1 : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
        H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) i.succ) p
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (partialD i (sharpFamily d lam)) p volume :=
  eLpNorm_testGraph_succ_eq measurableSet_ball (isTestFn_sharpFamily h0 h1) p i

/-- At the critical exponent the two powers of `lam` cancel: the renormalised dilates all have
the seminorm of the bump itself. -/
lemma eLpNorm_sharpFamily_crit {p' : ℝ≥0} (hp'0 : p' ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hd : 0 < d) (h0 : 0 < lam) :
    eLpNorm (sharpFamily d lam) (p' : ℝ≥0∞) volume
      = eLpNorm (⇑(sharpBump d)) (p' : ℝ≥0∞) volume := by
  rw [eLpNorm_sharpFamily h0 (by simpa using hp'0) (by simp)]
  have hp'R : ((p' : ℝ≥0∞)).toReal = (p' : ℝ) := by simp
  have hexp : 1 - (d : ℝ) / 2 + (d : ℝ) * (1 / ((p' : ℝ≥0∞)).toReal) = 0 := by
    have hp'' : (p' : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
      simpa using hp'
    rw [hp'R, one_div, hp'']
    have hdne : (d : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp, Real.rpow_zero, ENNReal.ofReal_one, one_mul]

/-- At the exponent `2` the renormalised dilates lose their norm linearly in `lam`. -/
lemma eLpNorm_sharpFamily_two (h0 : 0 < lam) :
    eLpNorm (sharpFamily d lam) 2 volume
      = ENNReal.ofReal lam * eLpNorm (⇑(sharpBump d)) 2 volume := by
  rw [eLpNorm_sharpFamily h0 two_ne_zero (by simp)]
  congr 2
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2, show 1 - (d : ℝ) / 2 + (d : ℝ) * (1 / 2) = 1 by ring, Real.rpow_one]

/-- The gradient coordinates keep their norm. -/
lemma eLpNorm_partialD_sharpFamily_two (h0 : 0 < lam) (i : Fin d) :
    eLpNorm (partialD i (sharpFamily d lam)) 2 volume
      = eLpNorm (partialD i (⇑(sharpBump d))) 2 volume := by
  rw [eLpNorm_partialD_sharpFamily h0 two_ne_zero (by simp) i]
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [h2, show 1 - (d : ℝ) / 2 - 1 + (d : ℝ) * (1 / 2) = 0 by ring, Real.rpow_zero,
    ENNReal.ofReal_one, one_mul]


/-! ### Sharpness -/

section Crit

variable {p' : ℝ≥0} [Fact (1 ≤ (p' : ℝ≥0∞))]

/-- The Sobolev embedding of `H₀¹` of the unit ball at the critical exponent. -/
def critEmb (d : ℕ) (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) →L[ℝ]
      Lp ℝ (p' : ℝ≥0∞) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  sobolevEmbL (fun _U hU => eLpNorm_le_of_mem_H01 measurableSet_ball hd hp' hU)

/-- `critEmb d hd hp' U` has the same `eLpNorm` as the function coordinate of `U`. -/
lemma eLpNorm_critEmb (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (q : ℝ≥0∞) :
    eLpNorm (⇑(critEmb d hd hp' U)) q (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = eLpNorm (((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))) 0) q
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
  eLpNorm_congr_ae (coeFn_sobolevEmbL _ U)

/-- `‖critEmb d hd hp' U‖` is the real `eLpNorm` of the function coordinate of `U` at
exponent `p'`. -/
lemma norm_critEmb (hd : 0 < d) (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ‖critEmb d hd hp' U‖
      = (eLpNorm (((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))) 0) (p' : ℝ≥0∞)
          (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))).toReal := by
  rw [Lp.norm_def, eLpNorm_critEmb]

end Crit

/-- **A bounded sequence with images of fixed norm that vanish under an injective map is no
compact family.** If `‖T xₙ‖ = c > 0` with `‖xₙ‖ ≤ 1`, and `S` is continuous and injective with
`S (T xₙ) → 0`, then `T` is not compact: a convergent subsequence of `T xₙ` would have a limit of
norm `c` which `S` sends to `0`. -/
theorem not_isCompactOperator_of_tendsto_zero {X Y Z : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (T : X →L[ℝ] Y) (S : Y →L[ℝ] Z) (hS : Function.Injective S) {x : ℕ → X}
    (hx : ∀ n, ‖x n‖ ≤ 1) {c : ℝ} (hc : 0 < c) (hT : ∀ n, ‖T (x n)‖ = c)
    (hlim : Filter.Tendsto (fun n => S (T (x n))) Filter.atTop (nhds 0)) :
    ¬ IsCompactOperator T := by
  intro hcpt
  have hcl := (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap
    one_pos).mp hcpt
  obtain ⟨v, -, ψ, hψ, hψtend⟩ := hcl.tendsto_subseq (x := fun n => T (x n))
    fun n => subset_closure ⟨x n, by simpa using hx n, rfl⟩
  have hv : ‖v‖ = c := tendsto_nhds_unique ((continuous_norm.tendsto v).comp hψtend)
    (by simp [Function.comp_def, hT])
  have hSv : S v = 0 := tendsto_nhds_unique ((S.continuous.tendsto v).comp hψtend)
    (hlim.comp hψ.tendsto_atTop)
  rw [hS (hSv.trans (map_zero S).symm), norm_zero] at hv
  exact hc.ne hv

/-- The norm of an element of `H1amb` is bounded by those of its coordinates. -/
lemma norm_H1amb_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (U : H1amb Ω) {a : ℝ}
    (ha : ‖U 0‖ ≤ a) {b : Fin d → ℝ} (hb : ∀ i, ‖U i.succ‖ ≤ b i) :
    ‖U‖ ≤ Real.sqrt (a ^ 2 + ∑ i, b i ^ 2) := by
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_succ]
  exact Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2)
    (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2))

/-- At the critical conjugate exponent `p' ≠ 0`, one has `2 ≤ p'`. -/
lemma two_le_of_sobolevConj {p' : ℝ≥0} (hp'0 : p' ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) : (2 : ℝ≥0) ≤ p' := by
  have hpos : (0 : ℝ) < p' := by exact_mod_cast pos_iff_ne_zero.mpr hp'0
  rw [← NNReal.coe_le_coe, NNReal.coe_ofNat]
  refine (inv_le_inv₀ hpos two_pos).mp ?_
  have : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  simp only [NNReal.coe_ofNat] at hp'
  linarith

/-- **Failure of compactness at the critical exponent.** The renormalised dilates
stay in the unit ball of `H₀¹`, keep the `L^{2⋆}` norm of the bump, and lose their `L²` norm, so
their images have no convergent subsequence.

Compactness below the critical exponent is `rellichEmbL_isCompact_of_lt`. This is where that
range stops. -/
theorem not_isCompactOperator_critEmb (_hd : 2 < d) (hdpos : 0 < d) {p' : ℝ≥0}
    [Fact (1 ≤ (p' : ℝ≥0∞))] (hp'0 : p' ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ¬ IsCompactOperator (critEmb d hdpos hp') := by
  have hfin : ∀ q : ℝ≥0∞, eLpNorm (⇑(sharpBump d)) q volume ≠ ⊤ := fun q =>
    ((sharpBump d).continuous.memLp_of_hasCompactSupport
      (μ := volume) (p := q) (sharpBump d).hasCompactSupport).eLpNorm_lt_top.ne
  have hbump : ∀ q : ℝ≥0∞, q ≠ 0 → 0 < (eLpNorm (⇑(sharpBump d)) q volume).toReal :=
    fun q hq => ENNReal.toReal_pos (eLpNorm_sharpBump_ne_zero hq) (hfin q)
  set a : ℝ := (eLpNorm (⇑(sharpBump d)) 2 volume).toReal with hadef
  set c : ℝ := (eLpNorm (⇑(sharpBump d)) (p' : ℝ≥0∞) volume).toReal with hcdef
  have ha0 : 0 < a := hbump 2 two_ne_zero
  have hc0 : 0 < c := hbump _ (by simpa using hp'0)
  -- The dilation parameters `1 / (n + 2)`, and the family they define.
  have hl0 : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 2) := fun n => by positivity
  have hl1 : ∀ n : ℕ, (1 : ℝ) / (n + 2) ≤ 1 / 2 := fun n =>
    one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hltend : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (nhds 0) := by
    simpa [Pi.inv_def, one_div] using (Filter.tendsto_atTop_add_const_right _ 2
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  set U : ℕ → H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    fun n => sharpElt d (hl0 n) (hl1 n) with hUdef
  set b : Fin d → ℝ := fun i => (eLpNorm (partialD i (⇑(sharpBump d))) 2 volume).toReal with hbdef
  have hzero : ∀ n, ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
      H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) 0‖ = 1 / ((n : ℝ) + 2) * a := fun n => by
    rw [Lp.norm_def, hUdef, eLpNorm_sharpElt_zero, eLpNorm_sharpFamily_two (hl0 n),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (hl0 n).le]
  have hsucc : ∀ n i, ‖((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
      H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) i.succ‖ = b i := fun n i => by
    rw [Lp.norm_def, hUdef, eLpNorm_sharpElt_succ, eLpNorm_partialD_sharpFamily_two (hl0 n)]
  -- The family is bounded in `H₀¹`, and its renormalisation `W` lies in the unit ball.
  set B : ℝ := Real.sqrt (a ^ 2 + ∑ i, (b i) ^ 2) with hBdef
  have hB0 : 0 < B := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hUbound : ∀ n, ‖U n‖ ≤ B := fun n =>
    norm_H1amb_le (Ω := ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      ((U n : H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :
        H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      (by rw [hzero n]; nlinarith [(hl0 n).le, hl1 n]) (fun i => (hsucc n i).le)
  set W : ℕ → H01 (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := fun n => B⁻¹ • U n with hWdef
  have hWball : ∀ n, ‖W n‖ ≤ 1 := fun n => by
    rw [hWdef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB0)]
    calc B⁻¹ * ‖U n‖ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hUbound n) (inv_pos.mpr hB0).le
      _ = 1 := inv_mul_cancel₀ hB0.ne'
  -- The images keep the fixed norm `B⁻¹ c` and lose their `L²` norm.
  have himg : ∀ n, ‖critEmb d hdpos hp' (W n)‖ = B⁻¹ * c := fun n => by
    rw [hWdef, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB0),
      norm_critEmb, hUdef, eLpNorm_sharpElt_zero, eLpNorm_sharpFamily_crit hp'0 hp' hdpos (hl0 n)]
  have h2p' : (2 : ℝ≥0∞) ≤ (p' : ℝ≥0∞) := by exact_mod_cast two_le_of_sobolevConj hp'0 hp'
  have hlim : Filter.Tendsto (fun n => lpInclusion (volume.restrict (ball
      (0 : EuclideanSpace ℝ (Fin d)) 1)) h2p' (critEmb d hdpos hp' (W n))) Filter.atTop
      (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hnorm : ∀ n, ‖lpInclusion (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
        h2p' (critEmb d hdpos hp' (W n))‖ = B⁻¹ * (1 / ((n : ℝ) + 2) * a) := fun n => by
      rw [hWdef, map_smul, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB0),
        Lp.norm_def, eLpNorm_congr_ae (coeFn_lpInclusion _ _ _), eLpNorm_critEmb, ← Lp.norm_def,
        hzero n]
    simpa [hnorm] using (hltend.mul_const a).const_mul B⁻¹
  exact not_isCompactOperator_of_tendsto_zero (critEmb d hdpos hp') _
    (lpInclusion_injective _ h2p') hWball (mul_pos (inv_pos.mpr hB0) hc0) himg hlim

end EllipticPdes.Embedding
