/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Embedding.WeakGradient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Average

/-!
# Ray fundamental theorem of calculus

For a smooth function `φ`, the increment `φ (x + v) - φ x` equals the integral, over
`[0, 1]`, of the directional derivative `(fderiv ℝ φ (x + t • v)) v` along the segment
`t ↦ x + t • v`. This is the pointwise identity consumed by the potential-estimate step
of the Morrey embedding.
-/

open MeasureTheory Set Metric
open scoped NNReal

noncomputable section

namespace EllipticDirichlet.Embedding

variable {d : ℕ}

/-- The segment path `t ↦ φ (x + t • v)` has derivative `(fderiv ℝ φ (x + t • v)) v`. -/
private theorem hasDerivAt_comp_segment {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ((fderiv ℝ φ (x + t • v)) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (x + t • v)) (x + t • v) :=
    (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact hφ'.comp_hasDerivAt t hline

/-- **Ray fundamental theorem of calculus.** For smooth `φ`, the increment along the
segment from `x` to `x + v` is the integral of the directional derivative. -/
theorem sub_eq_intervalIntegral_fderiv {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x v : EuclideanSpace ℝ (Fin d)) :
    φ (x + v) - φ x = ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • v)) v := by
  have hcont : Continuous (fun t : ℝ => (fderiv ℝ φ (x + t • v)) v) :=
    ((hφ.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hasDerivAt_comp_segment hφ x v t)
        hcont.continuousOn.intervalIntegrable]
  simp

/-- **Ray-FTC average identity (Morrey rung 4a).** For smooth `φ`, the oscillation of the
ball-average of `φ` about the value `φ x` equals the average over the ball of the ray
integral of the directional derivative from `x` towards the running point `y`. This is the
mechanical half of the potential estimate: it rewrites the oscillation as an average of
gradient line-integrals, from which the kernel bound is read off. -/
theorem oscillation_eq_average_ray [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (c x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    (⨍ y in ball c r, φ y) - φ x
      = ⨍ y in ball c r, ∫ t in (0 : ℝ)..1, (fderiv ℝ φ (x + t • (y - x))) (y - x) := by
  have hmeas : MeasurableSet (ball c r) := measurableSet_ball
  have hpos : volume (ball c r) ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hlt : volume (ball c r) < ⊤ := measure_ball_lt_top
  have htop := hlt.ne
  -- Pointwise: replace the inner ray integral by `φ y - φ x` via Task 3.
  have hcongr : (⨍ y in ball c r, ∫ t in (0 : ℝ)..1,
      (fderiv ℝ φ (x + t • (y - x))) (y - x))
      = ⨍ y in ball c r, (φ y - φ x) := by
    refine setAverage_congr_fun hmeas ?_
    filter_upwards with y _
    have h := (sub_eq_intervalIntegral_fderiv hφ x (y - x)).symm
    rwa [add_sub_cancel] at h
  rw [hcongr]
  -- `φ` is integrable on the ball (continuous, ball has finite measure).
  have hint : IntegrableOn φ (ball c r) volume :=
    (hφ.continuous.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  -- Split the average of the difference.
  rw [setAverage_eq, setAverage_eq, integral_sub hint (integrableOn_const htop),
    smul_sub, setIntegral_const, smul_smul]
  have hk : (volume.real (ball c r))⁻¹ * volume.real (ball c r) = 1 :=
    inv_mul_cancel₀ (by
      simp only [measureReal_def, ne_eq, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hpos, htop⟩)
  rw [hk, one_smul]

/-- **Region fact.** If `x, y` both lie in `ball c r` and `0 < t`, then the segment point
`x + t • (y - x)` is within distance `2 r t` of `x`. This is the geometric input feeding the
Riesz-kernel tail bound: after the affine change of variables the transformed region
`B_t = x + t • (ball c r - x)` sits inside the ball `‖z - x‖ < 2 r t`. -/
private theorem norm_smul_sub_lt_two_mul {c x y : EuclideanSpace ℝ (Fin d)} {r t : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) (ht : 0 < t) :
    ‖t • (y - x)‖ < 2 * r * t := by
  have hyx : ‖y - x‖ < 2 * r := by
    have htri : dist y x ≤ dist y c + dist c x := dist_triangle y c x
    have h1 : dist y c < r := by rwa [mem_ball] at hy
    have h2 : dist c x < r := by rw [dist_comm]; rwa [mem_ball] at hx
    have : dist y x < 2 * r := by linarith
    rwa [dist_eq_norm] at this
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc t * ‖y - x‖ < t * (2 * r) := by exact mul_lt_mul_of_pos_left hyx ht
    _ = 2 * r * t := by ring

/-- **Tail bound.** For `a > 0` and dimension `d ≥ 1`, the interval integral of the singular
kernel `t ^ (-(d+1))` from `a` to `1` is bounded by `a^{-d} / d`. Applied with
`a = ‖z - x‖ / (2 r)` this produces the Riesz-kernel factor `(2 r)^d / (d ‖z - x‖^d)`. -/
private theorem tail_integral_bound (hd : 0 < d) {a : ℝ} (ha : 0 < a) :
    ∫ t in a..(1 : ℝ), t ^ (-((d : ℤ) + 1)) ≤ a ^ (-(d : ℤ)) / d := by
  have hne : (-((d : ℤ) + 1)) ≠ -1 := by
    have : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    omega
  have h0 : (0 : ℝ) ∉ Set.uIcc a 1 := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  rw [integral_zpow (Or.inr ⟨hne, h0⟩)]
  have hexp : (-((d : ℤ) + 1)) + 1 = -(d : ℤ) := by ring
  rw [hexp]
  have hA : (0 : ℝ) < a ^ (-(d : ℤ)) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hden : (((-((d : ℤ) + 1)) : ℤ) : ℝ) + 1 = -(d : ℝ) := by push_cast; ring
  have key : (1 - a ^ (-(d : ℤ))) / (-(d : ℝ)) = (a ^ (-(d : ℤ)) - 1) / (d : ℝ) := by
    rw [div_neg]; ring
  rw [hden, one_zpow, key, div_le_div_iff_of_pos_right hdR]
  linarith

end EllipticDirichlet.Embedding
