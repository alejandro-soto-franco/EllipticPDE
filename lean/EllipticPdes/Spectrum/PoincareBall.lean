/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.PoincareWirtinger
public import EllipticPdes.Extension.GraphOperator
public import EllipticPdes.Extension.Translate
public import EllipticPdes.Analysis.Dilation

/-!
# Poincaré's inequality on a ball

Evans §5.8.1 Theorem 2: one constant, depending on the dimension alone at `p = 2`, bounds the
`L²` distance of a class on any ball from its mean over that ball by the radius times the `L²`
norm of its gradient. The case of the unit ball is `poincare_wirtinger_ball`; the general ball
is taken onto it by the affine map `y ↦ r y + x`, under which Lebesgue measure scales by
`r^d`, the mean is unchanged, a weak gradient picks up the factor `r`, and the `L²` seminorm
on the unit ball is the seminorm on the ball scaled by `r^{-d/2}`, which cancels between the
two sides.

The affine map is a measure-preserving map from the unit ball with Lebesgue measure to the
ball with Lebesgue measure scaled by `r^{-d}`, which is what makes every transport a one-line
application of Mathlib's `MeasurePreserving` API.

## Main declarations

* `EllipticPdes.Sobolev.affineBall`: the map `y ↦ r y + x`.
* `EllipticPdes.Sobolev.measurePreserving_affineBall`: its measure transport.
* `EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall`: a weak gradient transported through
  it.
* `EllipticPdes.Sobolev.poincare_ball`: the inequality.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.8.1 Theorem 2 (p. 291).
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Analysis (partialD_comp_smul)
open EllipticPdes.Extension (hasC1Boundary_ball exists_W12_of_hasWeakGradOn partialD_comp_translate)

variable {d : ℕ}

/-! ### The affine map of the unit ball onto a ball -/

/-- The map `y ↦ r y + x` of the unit ball onto the ball of centre `x` and radius `r`. -/
def affineBall (x : EuclideanSpace ℝ (Fin d)) (r : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := r • y + x

/-- The preimage of `ball x r` under `affineBall x r` is the open unit ball. -/
theorem affineBall_preimage_ball (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    affineBall x r ⁻¹' ball x r = ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
  ext y
  simp only [affineBall, mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, sub_zero]
  constructor <;> intro h <;> nlinarith [norm_nonneg y]

/-- `affineBall x r` is a measurable embedding for `r ≠ 0`. -/
theorem measurableEmbedding_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : r ≠ 0) :
    MeasurableEmbedding (affineBall x r) :=
  (Homeomorph.addRight x).measurableEmbedding.comp (MeasurableEquiv.smul₀ r hr).measurableEmbedding

/-- The factor by which Lebesgue measure scales under the map, as a measure multiplier. -/
def ballScale (d : ℕ) (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal |(r ^ d)⁻¹|

/-- `ballScale d r` is nonzero for `0 < r`. -/
theorem ballScale_ne_zero {r : ℝ} (hr : 0 < r) : ballScale d r ≠ 0 := by
  rw [ballScale, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

/-- `ballScale d r` is finite. -/
theorem ballScale_ne_top (r : ℝ) : ballScale d r ≠ ⊤ := ENNReal.ofReal_ne_top

/-- `ballScale d r` has real value `(r ^ d)⁻¹` for `0 < r`. -/
theorem ballScale_toReal {r : ℝ} (hr : 0 < r) : (ballScale d r).toReal = (r ^ d)⁻¹ := by
  rw [ballScale, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity)]

/-- **Measure transport of the affine map.** From the unit ball with Lebesgue measure to the
ball with Lebesgue measure scaled by `r^{-d}`. -/
theorem measurePreserving_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    MeasurePreserving (affineBall x r) (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      (ballScale d r • volume.restrict (ball x r)) := by
  have h1 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => r • y) volume
      (ballScale d r • volume) :=
    ⟨measurable_const_smul r, by
      rw [Measure.map_addHaar_smul volume hr.ne', finrank_euclideanSpace_fin]; rfl⟩
  have h2 : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin d) => y + x)
      (ballScale d r • volume) (ballScale d r • volume) :=
    (measurePreserving_add_right volume x).smul_measure _
  have h3 : MeasurePreserving (affineBall x r) volume (ballScale d r • volume) := h2.comp h1
  have h4 := h3.restrict_preimage (s := ball x r) measurableSet_ball
  rwa [affineBall_preimage_ball x hr, Measure.restrict_smul] at h4

/-- Transport of an integral over the ball. -/
theorem integral_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (affineBall x r y)
      = (ballScale d r).toReal * ∫ z in ball x r, f z := by
  rw [(measurePreserving_affineBall x hr).integral_comp (measurableEmbedding_affineBall x hr.ne')
    f, integral_smul_measure, smul_eq_mul]

/-- Transport of an `L²` seminorm over the ball. -/
theorem eLpNorm_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : AEStronglyMeasurable f (volume.restrict (ball x r))) :
    eLpNorm (f ∘ affineBall x r) 2 (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
      = ballScale d r ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm f 2 (volume.restrict (ball x r)) := by
  rw [eLpNorm_comp_measurePreserving (hf.smul_measure _) (measurePreserving_affineBall x hr),
    eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hf, smul_eq_mul]

/-- The square root of the scale factor of the affine map is a positive real. -/
theorem ballScale_rpow_half_toReal_pos {r : ℝ} (hr : 0 < r) :
    0 < (ballScale d r ^ (1 / (2 : ℝ≥0∞)).toReal).toReal := by
  refine ENNReal.toReal_pos ?_ (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg
    (ballScale_ne_top r))
  rw [ne_eq, ENNReal.rpow_eq_zero_iff]
  simp only [not_or, not_and]
  exact ⟨fun h => absurd h (ballScale_ne_zero hr), fun h => absurd h (ballScale_ne_top r)⟩

/-- The mean over the ball is the mean over the unit ball of the transported function. -/
theorem average_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    ⨍ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (affineBall x r y) = ⨍ z in ball x r, f z := by
  rw [setAverage_eq, setAverage_eq, integral_comp_affineBall x hr, smul_eq_mul, smul_eq_mul,
    measureReal_def, measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ballScale_toReal hr]
  have hV : (volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (isOpen_ball.measure_pos volume (nonempty_ball.mpr one_pos)).ne'
      measure_ball_lt_top.ne).ne'
  have hr' : r ^ d ≠ 0 := by positivity
  field_simp

/-! ### The weak gradient through the affine map -/

/-- **A test function on the unit ball pushed forward to the ball.** A smooth test function `φ`
supported in the unit ball is `ψ ∘ affineBall x r` for a smooth `ψ` with compact support in the
ball `B(x, r)`, and `∂ₖψ ∘ affineBall x r = r⁻¹ ∂ₖφ`. -/
theorem exists_affineBall_pushforward (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ)
    (hφB : tsupport φ ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) 1) (k : Fin d) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ ball x r ∧ (∀ y, ψ (affineBall x r y) = φ y) ∧
      ∀ y, partialD k ψ (affineBall x r y) = r⁻¹ * partialD k φ y := by
  have hr0 : r ≠ 0 := hr.ne'
  -- the test function pushed forward to the ball
  set ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => φ (r⁻¹ • (z + -x)) with hψ
  have hF : Differentiable ℝ fun w : EuclideanSpace ℝ (Fin d) => φ (r⁻¹ • w) := by
    intro w
    exact ((hφc.differentiable (by simp)) _).comp w (differentiableAt_id.const_smul r⁻¹)
  have hψc : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφc.comp ((contDiff_id.add contDiff_const).const_smul r⁻¹)
  have hψcs : HasCompactSupport ψ := by
    have := hφcs.comp_homeomorph
      ((Homeomorph.addRight (-x)).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0)))
    exact this
  have hψB : tsupport ψ ⊆ ball x r := by
    obtain ⟨ρ, ⟨hρ0, hρ1⟩, hK⟩ := exists_pos_lt_subset_ball one_pos hφcs.isClosed hφB
    refine (closure_minimal ?_ isClosed_closedBall).trans
      (closedBall_subset_ball (by nlinarith : r * ρ < r))
    intro z hz
    have h1 : r⁻¹ • (z + -x) ∈ tsupport φ := subset_tsupport _ hz
    have h2 := hK h1
    rw [mem_ball, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr] at h2
    rw [mem_closedBall, dist_eq_norm, ← sub_eq_add_neg] at *
    exact ((inv_mul_lt_iff₀ hr).mp h2).le
  -- the partial derivative of the pushed-forward test function
  have hψd : ∀ z, partialD k ψ z = r⁻¹ * partialD k φ (r⁻¹ • (z + -x)) := by
    intro z
    have h1 : partialD k ψ z
        = partialD k (fun w : EuclideanSpace ℝ (Fin d) => φ (r⁻¹ • w)) (z + -x) :=
      partialD_comp_translate hF (-x) k z
    rw [h1, partialD_comp_smul (hφc.differentiable (by simp)) r⁻¹ k]
  have hA : ∀ y : EuclideanSpace ℝ (Fin d), r⁻¹ • (affineBall x r y + -x) = y := by
    intro y
    simp only [affineBall, add_neg_cancel_right, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  have hψdA : ∀ y, partialD k ψ (affineBall x r y) = r⁻¹ * partialD k φ y := fun y => by
    rw [hψd, hA]
  -- transport of the two integrals
  exact ⟨ψ, hψc, hψcs, hψB, fun y => by simp only [hψ, hA], hψdA⟩

/-- **Weak gradient transported through the affine map**, which picks up the factor `r`. A test
function on the unit ball is pushed forward to one on the ball, whose partial derivative is
`r⁻¹` times the original's, and the integrals transport by the measure-preserving map. -/
theorem hasWeakGradOn_comp_affineBall (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hw : HasWeakGradOn (ball x r) u g) :
    HasWeakGradOn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) (u ∘ affineBall x r)
      fun k y => r * g k (affineBall x r y) := by
  intro φ hφc hφcs hφB k
  obtain ⟨ψ, hψc, hψcs, hψB, hψA, hψdA⟩ := exists_affineBall_pushforward x hr hφc hφcs hφB k
  have hkey := hw ψ hψc hψcs hψB k
  have hc0 : 0 < (ballScale d r).toReal :=
    ENNReal.toReal_pos (ballScale_ne_zero hr) (ballScale_ne_top r)
  have e1 : ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (u ∘ affineBall x r) y * partialD k φ y
      = r * ((ballScale d r).toReal * ∫ z in ball x r, u z * partialD k ψ z) := by
    rw [← integral_comp_affineBall x hr, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Function.comp_apply, hψdA]
    field_simp
  have e2 : ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) 1, r * g k (affineBall x r y) * φ y
      = r * ((ballScale d r).toReal * ∫ z in ball x r, g k z * ψ z) := by
    rw [← integral_comp_affineBall x hr, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hψA]
    ring
  rw [e1, e2, hkey]
  ring

/-! ### The inequality -/

/-- The unit ball, as a local abbreviation for the proof below. -/
local notation "B₁" => Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- **Transport of a class on a ball to the unit ball.** For a class `u` on `ball x r` with an `L²`
weak gradient `g`, pulling back along the affine map from the unit ball gives an element of
`W12` of the unit ball whose distance from its mean is a constant `s` times that of `u`, and
whose gradient coordinates are `r s` times those of `g`. -/
theorem exists_W12_transport_ball (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball x r)))
    (hg : ∀ k, MemLp (g k) 2 (volume.restrict (ball x r))) (hw : HasWeakGradOn (ball x r) u g) :
    ∃ s : ℝ, 0 < s ∧ ∃ U : W12 (ball (0 : EuclideanSpace ℝ (Fin d)) 1),
      ‖embW12 _ U - constL2 isBounded_ball (meanL2 isBounded_ball (embW12 _ U))‖
        = s * (eLpNorm (fun y => u y - ⨍ z in ball x r, u z) 2
          (volume.restrict (ball x r))).toReal ∧
      ∀ k : Fin d, ‖(U : H1amb (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) k.succ‖
        = r * s * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal := by
  classical
  set s : ℝ≥0∞ := ballScale d r ^ (1 / (2 : ℝ≥0∞)).toReal with hs
  have hspos : 0 < s.toReal := ballScale_rpow_half_toReal_pos hr
  have hMP := measurePreserving_affineBall x hr
  -- the transported class and its gradient
  have hv : MemLp (u ∘ affineBall x r) 2 (volume.restrict B₁) :=
    (hu.smul_measure (ballScale_ne_top r)).comp_measurePreserving hMP
  have hh : ∀ k, MemLp (fun y => r * g k (affineBall x r y)) 2 (volume.restrict B₁) := fun k =>
    (((hg k).smul_measure (ballScale_ne_top r)).comp_measurePreserving hMP).const_mul r
  have hwg : HasWeakGradOn B₁ (u ∘ affineBall x r) fun k y => r * g k (affineBall x r y) :=
    hasWeakGradOn_comp_affineBall x hr hw
  obtain ⟨U, hU0, hUk⟩ := exists_W12_of_hasWeakGradOn hv hh hwg
  -- the mean of the transported class is the mean over the ball
  set m : ℝ := ⨍ z in ball x r, u z with hm
  have hmean : meanL2 isBounded_ball (embW12 B₁ U) = m := by
    rw [embW12_apply]
    rw [hU0, meanL2_apply, integral_congr_ae hv.coeFn_toLp, hm, ← average_comp_affineBall x hr,
      setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  -- the left side
  have hL : ‖embW12 B₁ U
        - constL2 isBounded_ball (meanL2 isBounded_ball (embW12 B₁ U))‖
      = s.toReal * (eLpNorm (fun y => u y - m) 2 (volume.restrict (ball x r))).toReal := by
    rw [hmean, embW12_apply]
    change ‖(U : H1amb B₁) 0 - constL2 isBounded_ball m‖ = _
    rw [hU0, Lp.norm_def]
    have hae : ((hv.toLp (u ∘ affineBall x r) - constL2 isBounded_ball m : L2D B₁) :
        EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict B₁] (fun y => u y - m) ∘ affineBall x r := by
      filter_upwards [Lp.coeFn_sub (hv.toLp (u ∘ affineBall x r)) (constL2 isBounded_ball m),
        hv.coeFn_toLp,
        coeFn_constL2 isBounded_ball m] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
      rfl
    have hasm : AEStronglyMeasurable (fun y => u y - m) (volume.restrict (ball x r)) :=
      hu.aestronglyMeasurable.sub aestronglyMeasurable_const
    rw [eLpNorm_congr_ae hae, eLpNorm_comp_affineBall x hr hasm, ENNReal.toReal_mul]
  -- the right side
  have hR : ∀ k : Fin d, ‖(U : H1amb B₁) k.succ‖
      = r * s.toReal * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal := by
    intro k
    rw [hUk, Lp.norm_toLp]
    have : (fun y => r * g k (affineBall x r y)) = r • (g k ∘ affineBall x r) := by
      funext y; simp [Pi.smul_apply, smul_eq_mul]
    rw [this, eLpNorm_const_smul, eLpNorm_comp_affineBall x hr (hg k).aestronglyMeasurable,
      ENNReal.toReal_mul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
      ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hr]
    ring
  refine ⟨s.toReal, hspos, U, hL, hR⟩

/-- **Poincaré's inequality on a ball** (Evans §5.8.1 Theorem 2 at `p = 2`). One constant,
depending on the dimension alone, bounds the `L²` distance of a class on any ball from its
mean over the ball by the radius times the `L²` norm of its gradient. -/
theorem poincare_ball (hd : 0 < d) :
    ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        MemLp u 2 (volume.restrict (ball x r)) →
        (∀ k, MemLp (g k) 2 (volume.restrict (ball x r))) →
        HasWeakGradOn (ball x r) u g →
        (eLpNorm (fun y => u y - ⨍ z in ball x r, u z) 2 (volume.restrict (ball x r))).toReal
          ≤ C * r * Real.sqrt (∑ k, (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal ^ 2) := by
  obtain ⟨C, hC⟩ := poincare_wirtinger_ball hd
  refine ⟨C, fun x r hr u g hu hg hw => ?_⟩
  obtain ⟨s, hs, U, hL, hR⟩ := exists_W12_transport_ball x hr hu hg hw
  have hineq := hC U
  rw [hL] at hineq
  simp only [hR] at hineq
  -- divide by the common factor
  have hsum : Real.sqrt (∑ k : Fin d,
      (r * s * (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal) ^ 2)
      = r * s * Real.sqrt (∑ k, (eLpNorm (g k) 2 (volume.restrict (ball x r))).toReal ^ 2) := by
    simp_rw [mul_pow (r * s)]
    rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hsum] at hineq
  refine le_of_mul_le_mul_left ?_ hs
  linarith [hineq]

end EllipticPdes.Sobolev
