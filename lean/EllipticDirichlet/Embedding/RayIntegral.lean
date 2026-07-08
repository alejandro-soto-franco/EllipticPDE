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

end EllipticDirichlet.Embedding
