/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Embedding
public import EllipticPdes.NormedDivForm.Graph
public import EllipticPdes.Spectrum.RellichW12Haar
public import EllipticPdes.Extension.C1Invariance

/-!
# Rellich on `W^{1,2}(Ω)` on a normed space

For a bounded open set with `C¹` boundary in a finite-dimensional real normed space with an
additive Haar measure, the embedding `W^{1,2}(Ω) ↪ L²(Ω)` is compact. `graphTransfer` sends
`W^{1,2}(Ω)` into `W^{1,2}` of the Euclidean image, whose boundary is `C¹` by the definition of
`Extension.HasC1BoundaryNormed`, and `H1Graph.embW12G_isCompact_haar` applies there.

## Main declarations

* `EllipticPdes.NormedDivForm.graphTransferW12`
* `EllipticPdes.NormedDivForm.isCompactOperator_fnL_W12`
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

local notation "𝓛" => (toEuclidean (E := E))

variable (μ Ω) in
/-- The graph transfer restricted to `W^{1,2}(Ω)`. -/
def graphTransferW12 : W1pGraph.W12 μ Ω →L[ℝ] H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) :=
  ((graphTransfer μ Ω : W1pGraph 2 μ Ω →L[ℝ] H1Graph (μ.map 𝓛) (𝓛 '' Ω)).comp
    (W1pGraph.W12 μ Ω).subtypeL).codRestrict _ fun U => graphTransfer_mem_W12 Ω U.2

omit [μ.IsAddHaarMeasure] in
/-- The function part of a graph is the inverse transfer of the function part of its image. -/
lemma fnL_eq_transferLp_symm_graph (U : W1pGraph 2 μ Ω) :
    W1pGraph.fnL U = (transferLp μ Ω).symm (H1Graph.fnL (graphTransfer μ Ω U)) :=
  ((transferLp μ Ω).symm_apply_eq.2 (by
    rw [transferLp_apply]
    exact Lp.ext ((fnL_graphTransfer_symm_ae Ω U).trans
      (Lp.coeFn_compMeasurePreserving _ _).symm))).symm

/-- **Rellich on `W^{1,2}(Ω)` on a normed space.** For a bounded open set with `C¹` boundary in a
finite-dimensional real normed space of positive dimension with an additive Haar measure, the
embedding `W^{1,2}(Ω) ↪ L²(Ω)` is compact. -/
theorem isCompactOperator_fnL_W12 (hd : 0 < finrank ℝ E) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1BoundaryNormed Ω) :
    IsCompactOperator ((W1pGraph.fnL (p := 2) (μ := μ) (Ω := Ω)).comp
      (W1pGraph.W12 μ Ω).subtypeL) := by
  convert ((H1Graph.embW12G_isCompact_haar hd (μ.map 𝓛)
      (show IsOpen (𝓛 '' Ω) from (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩo)
      (isBounded_toEuclidean_image hΩb) hC1).clm_comp
        (transferLp μ Ω).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp_clm
      (graphTransferW12 μ Ω) using 1
  exact funext fun U => fnL_eq_transferLp_symm_graph (U : W1pGraph 2 μ Ω)

end NormedDivForm

end EllipticPdes
