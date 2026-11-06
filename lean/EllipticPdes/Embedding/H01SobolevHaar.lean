/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.DivFormMaximumTransport
public import EllipticPdes.Spectrum.RellichHaar

/-!
# Sobolev inequality on `H₀¹` for any additive Haar measure

`H1Graph.exists_eLpNorm_le_of_mem_H01` is stated for the canonical volume. An additive Haar measure
is `c • volume`. Under the identity on representatives the `L^q` seminorm scales by `c^(1/q)` and
the `L²` norm of the gradient by `√c`, so the inequality holds for `c • volume` with the constant
multiplied by `c^(1/q) / √c`.

## Main declarations

* `EllipticPdes.H1Graph.exists_eLpNorm_le_of_mem_H01_haar`
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.H1Graph

section Scaling

variable {α : Type*} [MeasurableSpace α] {ρ ρ' : Measure α} {c : ℝ≥0}

/-- The `L^q` seminorm against `c • ρ` is `c ^ (1/q)` times the seminorm against `ρ`. -/
lemma Internal.toReal_eLpNorm_smul_measure (q : ℝ≥0) {f : α → ℝ}
    (hf : AEStronglyMeasurable f ρ) :
    (eLpNorm f q (c • ρ)).toReal = (c : ℝ) ^ (1 / (q : ℝ)) * (eLpNorm f q ρ).toReal := by
  rw [ENNReal.smul_def, eLpNorm_smul_measure_of_ne_top ENNReal.coe_ne_top f _ hf, smul_eq_mul,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
  simp

/-- The `L^q` seminorm on `s` against `c • ρ` is `c ^ (1/q)` times the seminorm against `ρ`. -/
lemma Internal.toReal_eLpNorm_restrict_smul (q : ℝ≥0) {s : Set α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f (ρ.restrict s)) :
    (eLpNorm f q ((c • ρ).restrict s)).toReal =
      (c : ℝ) ^ (1 / (q : ℝ)) * (eLpNorm f q (ρ.restrict s)).toReal := by
  rw [Measure.restrict_smul]
  exact Internal.toReal_eLpNorm_smul_measure q hf

/-- Membership of `L^q` on `s` passes from `ρ` to `c • ρ`. -/
lemma Internal.memLp_restrict_smul {q : ℝ≥0∞} {s : Set α} {f : α → ℝ}
    (hf : MemLp f q (ρ.restrict s)) : MemLp f q ((c • ρ).restrict s) := by
  rw [Measure.restrict_smul]
  exact hf.smul_measure_nnreal

/-- The squared `L²` norm against `c • ρ` is `c` times the squared norm against `ρ`. -/
lemma Internal.norm_sq_eq_smul_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (hc : c ≠ 0) (h : ρ' = c • ρ) (g : Lp F 2 ρ') :
    ‖g‖ ^ 2 = c * ‖lpSmulL hc h g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_eq_smul_inner_lpSmulL hc h]

/-- The norm against `ρ` of the rescaled class is the norm against `c • ρ` divided by `√c`. -/
lemma Internal.norm_lpSmulL_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hc : c ≠ 0) (h : ρ' = c • ρ) (g : Lp F 2 ρ') :
    ‖lpSmulL hc h g‖ = ‖g‖ / √(c : ℝ) := by
  rw [eq_div_iff (Real.sqrt_ne_zero'.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc))),
    ← Real.sqrt_sq (norm_nonneg g), Internal.norm_sq_eq_smul_norm_sq hc h,
    Real.sqrt_mul (NNReal.coe_nonneg c), Real.sqrt_sq (norm_nonneg _), mul_comm]

end Scaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E} {c : ℝ≥0}

/-- One instance of the rescaled Sobolev inequality. -/
lemma Internal.eLpNorm_le_smul {q : ℝ≥0} {C : ℝ} (hc : c ≠ 0)
    (h : ∀ W : H01 (volume : Measure E) Ω,
      MemLp (⇑(fnL (W : H1Graph volume Ω))) q (volume.restrict Ω) ∧
        (eLpNorm (⇑(fnL (W : H1Graph volume Ω))) q (volume.restrict Ω)).toReal ≤
          C * ‖gradL (W : H1Graph volume Ω)‖)
    (V : H01 (c • (volume : Measure E)) Ω) :
    MemLp (⇑(fnL (V : H1Graph (c • volume) Ω))) q ((c • (volume : Measure E)).restrict Ω) ∧
      (eLpNorm (⇑(fnL (V : H1Graph (c • volume) Ω))) q
          ((c • (volume : Measure E)).restrict Ω)).toReal ≤
        (c : ℝ) ^ (1 / (q : ℝ)) * C / √(c : ℝ) * ‖gradL (V : H1Graph (c • volume) Ω)‖ := by
  obtain ⟨hm, hb⟩ := h (smulMeasureH01 c hc V)
  have hae := coeFn_lpSmulL hc (Measure.restrict_smul c volume Ω)
    (fnL (V : H1Graph (c • volume) Ω))
  refine ⟨Internal.memLp_restrict_smul (hm.ae_eq hae), ?_⟩
  rw [Internal.toReal_eLpNorm_restrict_smul q
    (Lp.aestronglyMeasurable _ |>.mono_ac (absolutelyContinuous_of_smul hc
      (Measure.restrict_smul c volume Ω))), ← eLpNorm_congr_ae hae]
  calc (c : ℝ) ^ (1 / (q : ℝ)) * (eLpNorm (⇑(fnL ((smulMeasureH01 c hc V : H01 volume Ω) :
          H1Graph volume Ω))) q (volume.restrict Ω)).toReal
      ≤ (c : ℝ) ^ (1 / (q : ℝ)) * (C * ‖gradL ((smulMeasureH01 c hc V : H01 volume Ω) :
          H1Graph volume Ω)‖) := by gcongr
    _ = (c : ℝ) ^ (1 / (q : ℝ)) * C / √(c : ℝ) * ‖gradL (V : H1Graph (c • volume) Ω)‖ := by
        rw [show gradL ((smulMeasureH01 c hc V : H01 volume Ω) : H1Graph volume Ω) =
          lpSmulL hc (Measure.restrict_smul c volume Ω) (gradL (V : H1Graph (c • volume) Ω))
          from rfl, Internal.norm_lpSmulL_eq]
        ring

/-- **Sobolev inequality on `H₀¹` for any additive Haar measure.** In dimension at least two, on a
bounded measurable set, `H₀¹(Ω)` embeds into `L^q(Ω)` for some `q > 2`, with
`‖v‖_q ≤ C ‖∇v‖₂`. -/
theorem exists_eLpNorm_le_of_mem_H01_haar (μ : Measure E) [μ.IsAddHaarMeasure]
    (hn : 2 ≤ Module.finrank ℝ E) (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ V : H01 μ Ω,
      MemLp (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω) ∧
        (eLpNorm (⇑(fnL (V : H1Graph μ Ω))) q (μ.restrict Ω)).toReal ≤
          C * ‖gradL (V : H1Graph μ Ω)‖ := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  obtain ⟨q, hq, C, hC, h⟩ := exists_eLpNorm_le_of_mem_H01 hn hΩm hΩb
  exact ⟨q, hq, (c : ℝ) ^ (1 / (q : ℝ)) * C / √(c : ℝ), by positivity,
    Internal.eLpNorm_le_smul hc h⟩

end EllipticPdes.H1Graph
