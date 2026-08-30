/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.C1Test
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# A cutoff along one coordinate

The extension by reflection is proved by testing away from the interface and letting the
excluded strip shrink. The cutoff that excludes it is a function of the `j`-th coordinate
alone: `slabCut j ε x` vanishes for `|xⱼ| ≤ ε`, is `1` for `|xⱼ| ≥ 2 ε`, and takes values in
`[0, 1]`. Its `j`-th partial derivative is `O(1/ε)` and supported in the strip, and its other
partial derivatives vanish, which is what keeps the limit clean in the directions along the
interface.

## Main declarations

* `EllipticPdes.Extension.slabCut`: the cutoff.
* `EllipticPdes.Extension.slabCut_eq_zero`, `EllipticPdes.Extension.slabCut_eq_one`: its values
  on the strip and away from it.
* `EllipticPdes.Extension.partialD_slabCut_of_ne`: it is constant along the interface.
* `EllipticPdes.Extension.norm_partialD_slabCut_le`: the `O(1/ε)` bound on the remaining
  partial derivative.
-/

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- The one-dimensional profile: `1` outside `(-2, 2)`, `0` on `[-1, 1]`, smooth, in `[0, 1]`. -/
def cutProfile : ℝ → ℝ := fun t => 1 - (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) t

theorem contDiff_cutProfile : ContDiff ℝ (⊤ : ℕ∞) cutProfile :=
  contDiff_const.sub (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).contDiff

theorem cutProfile_eq_zero {t : ℝ} (ht : |t| ≤ 1) : cutProfile t = 0 := by
  have : (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) t = 1 :=
    ContDiffBump.one_of_mem_closedBall _ (by simpa [Real.dist_eq] using ht)
  simp [cutProfile, this]

theorem cutProfile_eq_one {t : ℝ} (ht : 2 ≤ |t|) : cutProfile t = 1 := by
  have : (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) t = 0 :=
    ContDiffBump.zero_of_le_dist _ (by simpa [Real.dist_eq] using ht)
  simp [cutProfile, this]

theorem cutProfile_nonneg (t : ℝ) : 0 ≤ cutProfile t := by
  have := (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).le_one (x := t)
  simp only [cutProfile]
  linarith

theorem cutProfile_le_one (t : ℝ) : cutProfile t ≤ 1 := by
  have := (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).nonneg (x := t)
  simp only [cutProfile]
  linarith

/-- The profile's derivative is bounded, since it is continuous and constant off a compact
interval. -/
theorem exists_bound_deriv_cutProfile : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv cutProfile t| ≤ C := by
  have hcs : HasCompactSupport (deriv cutProfile) := by
    have hb : HasCompactSupport (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) :=
      (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).hasCompactSupport
    have hderiv : deriv cutProfile
        = fun t => -deriv (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) t := by
      funext t
      show deriv (fun t => 1 - (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)) t) t = _
      rw [deriv_const_sub]
    rw [hderiv]
    exact (hb.deriv).neg
  have hc : Continuous (deriv cutProfile) :=
    contDiff_cutProfile.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  exact ⟨C, le_trans (abs_nonneg _) (by simpa using hC 0), fun t => by simpa using hC t⟩

/-! ### The cutoff on the space -/

/-- **The cutoff excluding the slab `|xⱼ| ≤ ε`.** It depends on the `j`-th coordinate alone. -/
def slabCut (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ := cutProfile (x j / ε)

theorem contDiff_slabCut (j : Fin d) (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (slabCut j ε) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin d) => x j / ε) :=
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff).div_const ε
  exact contDiff_cutProfile.comp h

theorem slabCut_nonneg (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ slabCut j ε x := cutProfile_nonneg _

theorem slabCut_le_one (j : Fin d) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    slabCut j ε x ≤ 1 := cutProfile_le_one _

/-- On the excluded slab the cutoff vanishes. -/
theorem slabCut_eq_zero {j : Fin d} {ε : ℝ} (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin d)}
    (hx : |x j| ≤ ε) : slabCut j ε x = 0 := by
  refine cutProfile_eq_zero ?_
  rw [abs_div, abs_of_pos hε, div_le_one hε]
  exact hx

/-- Away from the slab the cutoff is `1`. -/
theorem slabCut_eq_one {j : Fin d} {ε : ℝ} (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin d)}
    (hx : 2 * ε ≤ |x j|) : slabCut j ε x = 1 := by
  refine cutProfile_eq_one ?_
  rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
  linarith

/-- The derivative of the cutoff, in every direction. -/
theorem partialD_slabCut {j : Fin d} {ε : ℝ} (hε : 0 < ε) (k : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (slabCut j ε) x
      = deriv cutProfile (x j / ε) * ((if j = k then (1 : ℝ) else 0) / ε) := by
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => y j / ε)
      = ⇑((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) := by
    funext y
    simp [div_eq_mul_inv, mul_comm]
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => y j / ε)
      ((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) x := by
    rw [hfun]
    exact ContinuousLinearMap.hasFDerivAt _
  have hc : HasDerivAt cutProfile (deriv cutProfile (x j / ε)) (x j / ε) :=
    (contDiff_cutProfile.differentiable (by simp) _).hasFDerivAt.hasDerivAt
  have hcomp : HasFDerivAt (slabCut j ε)
      ((deriv cutProfile (x j / ε)) •
        ((1 / ε) • (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))) x :=
    hc.comp_hasFDerivAt x hL
  rw [partialD, hcomp.fderiv]
  have hval : (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (EuclideanSpace.single k (1 : ℝ)) = if j = k then (1 : ℝ) else 0 := by
    simp [PiLp.single_apply]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hval]
  ring

/-- **The cutoff is constant along the interface.** -/
theorem partialD_slabCut_of_ne {j : Fin d} {ε : ℝ} (hε : 0 < ε) {k : Fin d} (hk : k ≠ j)
    (x : EuclideanSpace ℝ (Fin d)) : partialD k (slabCut j ε) x = 0 := by
  rw [partialD_slabCut hε k x, if_neg (Ne.symm hk)]
  simp

/-- **The remaining partial derivative is `O(1/ε)`.** -/
theorem norm_partialD_slabCut_le {j : Fin d} {ε : ℝ} (hε : 0 < ε) {C : ℝ}
    (hC : ∀ t, |deriv cutProfile t| ≤ C) (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    |partialD k (slabCut j ε) x| ≤ C / ε := by
  rw [partialD_slabCut hε k x, abs_mul]
  have h1 : |(if j = k then (1 : ℝ) else 0) / ε| ≤ 1 / ε := by
    rw [abs_div, abs_of_pos hε]
    gcongr
    split <;> simp
  have h0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 0)
  calc |deriv cutProfile (x j / ε)| * |(if j = k then (1 : ℝ) else 0) / ε|
      ≤ C * (1 / ε) := by
        exact mul_le_mul (hC _) h1 (abs_nonneg _) h0
    _ = C / ε := by ring

end EllipticPdes.Extension
