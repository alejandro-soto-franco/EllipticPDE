/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.GraphHaar
public import EllipticPdes.Spectrum.RellichGeneral

/-!
# The Rellich-Kondrachov theorem for any additive Haar measure

An additive Haar measure `μ` on a finite-dimensional real inner product space is `c • volume` for
a positive `c : ℝ≥0` (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Rescaling the measure
preserves compactness of the embedding (`H1Graph.embL2_isCompact_smul`), so the theorem for
`volume` (`H1Graph.embL2_isCompact`) gives the theorem for `μ`.

## Main declarations

* `EllipticPdes.H1Graph.exists_eq_smul_volume`: an additive Haar measure is a positive multiple of
  `volume`.
* `EllipticPdes.H1Graph.embL2_isCompact_haar`: `H₀¹(Ω) ↪ L²(Ω)` is compact for every bounded
  measurable `Ω` and every additive Haar measure.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

noncomputable section

namespace EllipticPdes.H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- An additive Haar measure is a positive multiple of `volume`. -/
theorem exists_eq_smul_volume (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • (volume : Measure E) :=
  ⟨Measure.addHaarScalarFactor μ volume,
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume).ne',
    Measure.isAddLeftInvariant_eq_smul μ volume⟩

/-- **Rellich-Kondrachov for any additive Haar measure.** For a bounded measurable set `Ω` in a
finite-dimensional real inner product space, the embedding `H₀¹(Ω) ↪ L²(Ω)` is compact. -/
theorem embL2_isCompact_haar (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Set E}
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    IsCompactOperator (embL2 μ Ω) := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  exact embL2_isCompact_smul c hc (embL2_isCompact hΩm hΩb)

end EllipticPdes.H1Graph
