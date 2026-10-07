/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.GraphIsometry
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Spectrum.RellichDischarge

/-!
# The Rellich-Kondrachov theorem on a finite-dimensional inner product space

For a bounded measurable `Ω` in a finite-dimensional real inner product space `E` with its
canonical volume, the embedding `H₀¹(Ω) ↪ L²(Ω)` of the graph space is compact. The coordinate
theorem `Sobolev.embL2_isCompact` gives the case `E = ℝⁿ`: `h01Equiv` identifies the two copies of
`H₀¹`. A linear isometry `E ≃ₗᵢ ℝⁿ` from an orthonormal basis then transports the general case to
the coordinate one through `H1Graph.mapH01` and `H1Graph.pushFn`.

## Main declarations

* `EllipticPdes.H1Graph.embL2_isCompact_euclidean`: the coordinate case, for the graph space.
* `EllipticPdes.H1Graph.embL2_isCompact`: the general case.
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace EllipticPdes.H1Graph

/-- **Rellich-Kondrachov on `ℝⁿ`, for the graph space.** The embedding `H₀¹(Ω) ↪ L²(Ω)` of a
bounded measurable set in `EuclideanSpace ℝ (Fin n)` is compact. -/
theorem embL2_isCompact_euclidean {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    IsCompactOperator (embL2 (volume : Measure (EuclideanSpace ℝ (Fin n))) Ω) := by
  have h := (Sobolev.embL2_isCompact hΩm hΩb).comp_clm
    (h01Equiv Ω).symm.toContinuousLinearEquiv.toContinuousLinearMap
  convert h using 1
  funext U
  change embL2 volume Ω U = Sobolev.embL2 Ω ((h01Equiv Ω).symm U)
  rw [Sobolev.embL2_apply, ← embL2_h01Equiv, LinearIsometryEquiv.apply_symm_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Set E}

/-- **Rellich-Kondrachov.** For a bounded measurable set `Ω` in a finite-dimensional real inner
product space, the embedding `H₀¹(Ω) ↪ L²(Ω)` of the graph space is compact. -/
theorem embL2_isCompact (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    IsCompactOperator (embL2 (volume : Measure E) Ω) := by
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) := (stdOrthonormalBasis ℝ E).repr
  have hm : MeasurableSet (e.symm ⁻¹' Ω) := e.symm.continuous.measurable hΩm
  have hb : Bornology.IsBounded (e.symm ⁻¹' Ω) :=
    e.symm.isometry.antilipschitzWith.isBounded_preimage hΩb
  have h := ((embL2_isCompact_euclidean hm hb).clm_comp
    (pushFn e Ω).toContinuousLinearMap).comp_clm (mapH01 e Ω)
  convert h using 1
  funext U
  simp [embL2_apply]

end EllipticPdes.H1Graph
