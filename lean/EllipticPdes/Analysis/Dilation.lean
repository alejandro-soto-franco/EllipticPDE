/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilations of a function

On a finite-dimensional real normed space with an additive Haar measure, scaling
`x ↦ f (r • x)` multiplies the `Lᵖ` seminorm by `|r|^{-n/p}` (`n` the dimension) and the
derivative by `r`, and it shrinks the support by `|r|⁻¹`. These are the three identities the
sharpness of the Sobolev embedding turns on: the exponent `p⋆` is the one at which the two
factors cancel, so a dilated family keeps its `L^{p⋆}` norm while its `L²` norm tends to zero.

## Main declarations

* `EllipticPdes.Analysis.eLpNorm_comp_smul_eq`: the `Lᵖ` seminorm of a dilate.
* `EllipticPdes.Analysis.fderiv_comp_smul`: the derivative of a dilate.
* `EllipticPdes.Analysis.tsupport_comp_smul_subset_closedBall`: the support of a dilate.
* `EllipticPdes.Analysis.eLpNorm_comp_smul` and `EllipticPdes.Analysis.partialD_comp_smul`: the
  same on `ℝᵈ`.

## References

Y. Guo, *Partial Differential Equations*, Example IV.2.11.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Analysis

open EllipticPdes.Sobolev

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- **`Lᵖ` seminorm of a dilate**, for an additive Haar measure on a finite-dimensional space.
Scaling the argument by `r` multiplies the seminorm by `|r^n|^{-1/p}`, `n` the dimension. -/
theorem eLpNorm_comp_smul_eq [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {f : E → F}
    (hf : StronglyMeasurable f) {r : ℝ} (hr : r ≠ 0) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (fun x => f (r • x)) p μ
      = ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| ^ (1 / p.toReal) * eLpNorm f p μ := by
  have hmeas : Measurable fun y : E => ‖f y‖ₑ ^ p.toReal := hf.enorm.pow_const _
  have hfr : AEStronglyMeasurable (fun x => f (r • x)) μ :=
    (hf.comp_measurable (measurable_const_smul r)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
    show (∫⁻ x, ‖f (r • x)‖ₑ ^ p.toReal ∂μ) = ∫⁻ y, ‖f y‖ₑ ^ p.toReal ∂(Measure.map (r • ·) μ) from
      (lintegral_map hmeas (measurable_const_smul r)).symm,
    Measure.map_addHaar_smul μ hr, lintegral_smul_measure, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]

variable [NormedSpace ℝ F]

/-- **Derivative of a dilate.** `D (f (r • ·)) x = r • Df (r • x)`. -/
theorem fderiv_comp_smul {f : E → F} (hf : Differentiable ℝ f) (r : ℝ) (x : E) :
    fderiv ℝ (fun x => f (r • x)) x = r • fderiv ℝ f (r • x) := by
  have hcomp : HasFDerivAt (fun x => f (r • x))
      ((fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ E)) x :=
    (hf (r • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  rw [hcomp.fderiv]
  ext v
  simp

omit [NormedSpace ℝ F] in
/-- **Support of a dilate.** For `0 < r`, a function supported in the closed unit ball dilates
to one supported in the closed ball of radius `r⁻¹`. -/
theorem tsupport_comp_smul_subset_closedBall {f : E → F} {r : ℝ} (hr : 0 < r)
    (hf : tsupport f ⊆ closedBall 0 1) :
    tsupport (fun x => f (r • x)) ⊆ closedBall 0 r⁻¹ := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  have := hf (subset_tsupport _ hx)
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr.le] at this
  rw [mem_closedBall_zero_iff, ← one_div, le_div_iff₀ hr, mul_comm]
  exact this

end General

variable {d : ℕ}

/-- **`Lᵖ` seminorm of a dilate** on `ℝᵈ`. Scaling the argument by `r` multiplies the seminorm
by `|r^d|^{-1/p}`. -/
theorem eLpNorm_comp_smul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    {r : ℝ} (hr : r ≠ 0) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    eLpNorm (fun x => f (r • x)) p volume
      = ENNReal.ofReal |(r ^ d)⁻¹| ^ (1 / p.toReal) * eLpNorm f p volume := by
  simpa using eLpNorm_comp_smul_eq (μ := volume) hf.stronglyMeasurable hr hp0 hpt

/-- **Partial derivatives of a dilate** on `ℝᵈ`, the coordinate form of `fderiv_comp_smul`. -/
theorem partialD_comp_smul {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Differentiable ℝ f)
    (r : ℝ) (i : Fin d) :
    partialD i (fun x => f (r • x)) = fun x => r * partialD i f (r • x) := by
  funext x
  simp [partialD, fderiv_comp_smul hf]

end EllipticPdes.Analysis
