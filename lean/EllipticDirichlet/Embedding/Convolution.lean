/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Young's `Lᵖ` inequality for a probability kernel

This file collects the reusable convolution machinery feeding the weak-gradient Morrey
embedding. The headline result `eLpNorm_convolution_le` is a specialised Young inequality:
convolving an `Lᵖ` function against a non-negative kernel of unit mass does not increase its
`Lᵖ` seminorm. The classical proof uses the (currently absent) Minkowski integral inequality;
we instead derive the pointwise bound directly from Hölder's inequality in `ℝ≥0∞` and close
with Tonelli, so no Minkowski inequality is required.

The mollifier kernel `φ.normed volume` is the intended instance (non-negative by
`ContDiffBump.nonneg_normed`, unit mass by `ContDiffBump.integral_normed`), and the restricted
corollary `eLpNorm_convolution_restrict_le` is the form consumed downstream.
-/

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution

noncomputable section

namespace EllipticDirichlet.Embedding

variable {d : ℕ}

/-- **Young's `Lᵖ` inequality for a probability kernel.** For `1 ≤ p`, a non-negative kernel
`ρ` with unit mass `∫ ρ = 1`, and `h ∈ Lᵖ`, the convolution against `ρ` does not increase the
`Lᵖ` seminorm: `‖h ⋆ ρ‖_{Lᵖ} ≤ ‖h‖_{Lᵖ}`. Proved by the pointwise Hölder bound
`|(h ⋆ ρ)(x)|^p ≤ ∫ |h(t)|^p ρ(x - t)` together with Tonelli and unit mass; no Minkowski
integral inequality is required. -/
theorem eLpNorm_convolution_le
    {p : ℝ} (hp : 1 ≤ p) {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p) volume
      ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hPreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  -- basic measurability of the enorms
  have hhen : AEMeasurable (fun z => ‖h z‖ₑ) volume := hh.aestronglyMeasurable.enorm
  have hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) volume := hρm.enorm
  -- the kernel is integrable, with unit `ℝ≥0∞`-mass
  have hρint : Integrable ρ volume := by
    by_contra hcon
    rw [integral_undef hcon] at hρ1
    exact one_ne_zero hρ1.symm
  have hmass : ∫⁻ z, ‖ρ z‖ₑ ∂volume = 1 := by
    have h1 : ∫⁻ z, ‖ρ z‖ₑ ∂volume = ∫⁻ z, ENNReal.ofReal (ρ z) ∂volume :=
      lintegral_congr fun z => Real.enorm_of_nonneg (hρ0 z)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun z => hρ0 z), hρ1,
      ENNReal.ofReal_one]
  -- measurability of the uncurried Tonelli integrand
  have hswapmeas : AEMeasurable
      (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖h q.2‖ₑ ^ p * ‖ρ (q.1 - q.2)‖ₑ) (volume.prod volume) :=
    ((hhen.pow_const p).comp_snd).mul
      (hρen.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  -- pointwise Hölder bound: `|(h ⋆ ρ)(x)|^p ≤ ∫ |h(t)|^p ρ(x - t)`
  have key : ∀ x, ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p
      ≤ ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
    intro x
    have hρxen : AEMeasurable (fun t => ‖ρ (x - t)‖ₑ) volume :=
      hρen.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
    have hwmass : ∫⁻ t, ‖ρ (x - t)‖ₑ ∂volume = 1 :=
      (lintegral_sub_left_eq_self (fun z => ‖ρ z‖ₑ) x).trans hmass
    have hbound : ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ
        ≤ ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t => ?_
      rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
    refine le_trans (ENNReal.rpow_le_rpow hbound hp0.le) ?_
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1, ENNReal.rpow_one]
      exact le_of_eq (lintegral_congr fun t => by rw [ENNReal.rpow_one])
    · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
      set q := Real.conjExponent p with hq_def
      have hq_pos : 0 < q := hpq.symm.pos
      have hsum : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
      have e1 : ∀ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p) * ‖ρ (x - t)‖ₑ ^ (1 / q)
          = ‖h t‖ₑ * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg, hsum,
          ENNReal.rpow_one]
      have e2 : ∀ t, (‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p)) ^ p
          = ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      have e3 : ∀ t, (‖ρ (x - t)‖ₑ ^ (1 / q)) ^ q = ‖ρ (x - t)‖ₑ := by
        intro t
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one]
      have hol : ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume
          ≤ (∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p) := by
        have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
          (hhen.mul (hρxen.pow_const (1 / p))) (hρxen.pow_const (1 / q))
        simp only [Pi.mul_apply] at hH
        rwa [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hwmass, ENNReal.one_rpow,
          mul_one] at hH
      calc (∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume) ^ p
          ≤ ((∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p)) ^ p :=
            ENNReal.rpow_le_rpow hol hp0.le
        _ = ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  -- reduce the seminorm inequality to the `lintegral` inequality
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop, hPreal]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hp0.le)
  calc ∫⁻ x, ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p ∂volume
      ≤ ∫⁻ x, ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume := lintegral_mono key
    _ = ∫⁻ t, ∫⁻ x, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume :=
        lintegral_lintegral_swap hswapmeas
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * ∫⁻ x, ‖ρ (x - t)‖ₑ ∂volume ∂volume := by
        refine lintegral_congr fun t => ?_
        have hmt : AEMeasurable (fun x => ‖ρ (x - t)‖ₑ) volume :=
          hρen.comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume t).quasiMeasurePreserving
        exact lintegral_const_mul'' (‖h t‖ₑ ^ p) hmt
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * 1 ∂volume := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_sub_right_eq_self (fun z => ‖ρ z‖ₑ) t, hmass]
    _ = ∫⁻ x, ‖h x‖ₑ ^ p ∂volume := by simp

/-- Young bound restricted to a set `s` on the left, upper-bounded by the full `Lᵖ` norm. -/
theorem eLpNorm_convolution_restrict_le {p : ℝ} (hp : 1 ≤ p)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume)
    (hρ1 : ∫ y, ρ y ∂volume = 1) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) (s : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p)
        (volume.restrict s)
      ≤ eLpNorm h (ENNReal.ofReal p) volume :=
  le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_convolution_le hp hρ0 hρm hρ1 hh)

end EllipticDirichlet.Embedding
