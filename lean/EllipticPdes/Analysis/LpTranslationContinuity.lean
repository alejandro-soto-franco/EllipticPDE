/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Continuity of translation in `Lᵖ`

An `Lᵖ` function is close in `Lᵖ` to its own translates by small vectors. This is the statement
the global approximation theorem shifts on: a function is moved into the domain by a small
translation, and the shift has to be small in the norm the approximation is measured in.

Mathlib states continuity of the action of `Eᵈᵃᵃ` on `Lᵖ` (`Lp.instContinuousVAddDomAddAct`),
and a translate is the action of the translation vector. The `eLpNorm` form follows from
continuity at zero.

## Main declarations

* `EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub'`: the `Lᵖ` distance to a translate tends
  to zero with the translation, on any finite-dimensional normed space with an additive Haar
  measure.
* `EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub`: the Euclidean case.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.3.3, Theorem 3; H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 4.3.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace EllipticPdes.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {p : ℝ≥0∞}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The `Lᵖ` norm of the difference of a function and its translate is the norm of the
difference of the classes. -/
theorem eLpNorm_translate_sub_eq {f : E → F} (hf : MemLp f p μ) (h : E)
    (hm : MemLp (fun y => f (h + y)) p μ) :
    eLpNorm (fun y => f (y + h) - f y) p μ
      = ENNReal.ofReal ‖hm.toLp (fun y => f (h + y)) - hf.toLp f‖ := by
  rw [← MemLp.toLp_sub, Lp.norm_toLp, ENNReal.ofReal_toReal (hm.sub hf).eLpNorm_ne_top]
  exact eLpNorm_congr_ae (Eventually.of_forall fun y => by simp [add_comm])

/-- **Continuity of translation in `Lᵖ`.** The `Lᵖ` distance between an `Lᵖ` function and its
translate tends to zero with the translation. -/
theorem tendsto_eLpNorm_translate_sub' (hp1 : 1 ≤ p) (hptop : p ≠ ∞) {f : E → F}
    (hf : MemLp f p μ) :
    Tendsto (fun h : E => eLpNorm (fun y => f (y + h) - f y) p μ) (𝓝 0) (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have : Fact (p ≠ ∞) := ⟨hptop⟩
  have hm : ∀ h : E, MemLp (fun y => f (h + y)) p μ := fun h =>
    hf.comp_measurePreserving (measurePreserving_add_left μ h)
  have hc : Continuous fun h : E => (hm h).toLp (fun y => f (h + y)) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk (continuous_const (y := hf.toLp f)))
  have h0 : Tendsto (fun h : E => ‖(hm h).toLp (fun y => f (h + y)) - hf.toLp f‖) (𝓝 0) (𝓝 0) := by
    simpa using ((hc.sub (continuous_const (y := hf.toLp f))).tendsto 0).norm
  simp_rw [eLpNorm_translate_sub_eq hf _ (hm _)]
  simpa using ENNReal.tendsto_ofReal h0

/-- **Continuity of translation in `Lᵖ`.** The `Lᵖ` distance between an `Lᵖ` function and its
translate tends to zero with the translation. -/
theorem tendsto_eLpNorm_translate_sub {d : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hptop : p ≠ ∞)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun h : EuclideanSpace ℝ (Fin d) =>
      eLpNorm (fun y => f (y + h) - f y) p volume) (𝓝 0) (𝓝 0) :=
  tendsto_eLpNorm_translate_sub' hp1 hptop hf

end EllipticPdes.Analysis
