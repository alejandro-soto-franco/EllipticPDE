/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The standard mollifying family

On a finite-dimensional real normed space `E` with an additive Haar measure `μ`, the family
`mollifier hr n` of bumps of outer radius `r / (n + 1)` mollifies any locally integrable
function `h : E → F` into a `C^∞` function, with compact support when `h` has compact support,
bounded by the supremum of `h`, and supported in the closed thickening of the support of `h` by
the radius of the bump.

## Main declarations

* `EllipticPdes.mollifier`: the bump of outer radius `r / (n + 1)` and inner radius half of it.
* `EllipticPdes.tendsto_rOut_mollifier`, `EllipticPdes.rOut_mollifier_le`: the radii shrink.
* `EllipticPdes.contDiff_normed_convolution`: a mollification is smooth.
* `EllipticPdes.norm_normed_convolution_le`: a mollification is bounded by what it mollifies.
* `EllipticPdes.tsupport_normed_convolution_subset`: the support of a mollification.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes

section Radii

variable {E : Type*} [NormedAddCommGroup E]

/-- The `n`-th bump of the standard mollifying family of scale `r`, of outer radius
`r / (n + 1)` and inner radius half of it. -/
def mollifier {r : ℝ} (hr : 0 < r) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := r / (n + 1) / 2
  rOut := r / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := half_lt_self (by positivity)

/-- The outer radius of `mollifier hr n` is `r / (n + 1)`. -/
@[simp] theorem rOut_mollifier {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rOut = r / (n + 1) := rfl

/-- The inner radius of `mollifier hr n` is `r / (n + 1) / 2`. -/
@[simp] theorem rIn_mollifier {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rIn = r / (n + 1) / 2 := rfl

/-- The bumps of the standard mollifying family have outer radius at most `r`. -/
theorem rOut_mollifier_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rOut ≤ r := by
  rw [rOut_mollifier]
  exact div_le_self hr.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- The outer radius of a standard mollifier is at most twice its inner radius. -/
theorem rOut_mollifier_le_two_mul_rIn {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (mollifier hr n : ContDiffBump (0 : E)).rOut
      ≤ 2 * (mollifier hr n : ContDiffBump (0 : E)).rIn :=
  le_of_eq (by simp only [rOut_mollifier, rIn_mollifier]; ring)

/-- The outer radii of the standard mollifying family tend to zero. -/
theorem tendsto_rOut_mollifier {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => (mollifier hr n : ContDiffBump (0 : E)).rOut) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r

end Radii

section Convolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The mollification of a locally integrable function is smooth. -/
theorem contDiff_normed_convolution (ρ : ContDiffBump (0 : E)) {h : E → F}
    (hh : LocallyIntegrable h μ) :
    ContDiff ℝ (⊤ : ℕ∞) (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) :=
  ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed hh

/-- The mollification of a compactly supported function has compact support. -/
theorem hasCompactSupport_normed_convolution (ρ : ContDiffBump (0 : E)) {h : E → F}
    (hh : HasCompactSupport h) :
    HasCompactSupport (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) :=
  HasCompactSupport.convolution _ ρ.hasCompactSupport_normed hh

/-- **Bound on a mollification by what it mollifies.** The normed bump is a probability
density, so the convolution is an average and inherits the bound. -/
theorem norm_normed_convolution_le (ρ : ContDiffBump (0 : E)) {h : E → F} (hc : Continuous h)
    {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M) (x : E) :
    ‖(ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] h) x‖ ≤ M := by
  have hex : ConvolutionExistsAt (ρ.normed μ) h x (ContinuousLinearMap.lsmul ℝ ℝ) μ :=
    ρ.hasCompactSupport_normed.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous hc.locallyIntegrable x
  rw [convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ (ρ.normed μ t)) (h (x - t)) ∂μ‖
      ≤ ∫ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ (ρ.normed μ t)) (h (x - t))‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t, ρ.normed μ t * M ∂μ := by
        refine integral_mono hex.norm (ρ.integrable_normed.mul_const M) fun t => ?_
        simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (ρ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left (hM _) (ρ.nonneg_normed t)
    _ = M := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- **Support of a mollification.** The mollification of a class of compact support is
supported in the closed thickening of that support by the radius of the bump. -/
theorem tsupport_normed_convolution_subset (ρ : ContDiffBump (0 : E)) {ψ : E → F}
    (hψ : HasCompactSupport ψ) :
    tsupport (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ψ)
      ⊆ cthickening ρ.rOut (tsupport ψ) := by
  refine closure_minimal ?_ isClosed_cthickening
  rw [← hψ.isCompact.closedBall_zero_add ρ.rOut_pos.le]
  refine (support_convolution_subset _).trans (Set.add_subset_add ?_ (subset_tsupport ψ))
  rw [ρ.support_normed_eq]
  exact ball_subset_closedBall

end Convolution

end EllipticPdes
