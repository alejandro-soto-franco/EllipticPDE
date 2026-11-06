/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Basic
public import EllipticPdes.SobolevP.GraphW12

/-!
# Divergence-form bilinear form on the graph space of a normed space

The transfer along `toEuclidean` extended from `W₀^{1,2}(Ω)` to the whole graph space
`W1pGraph 2 μ Ω`, and the bilinear form of a normed divergence-form operator on it. The graph
transfer sends `W^{1,2}(Ω)` into `H1Graph.W12` and restricts to `transferEquiv` on `W₀^{1,2}(Ω)`.

## Main declarations

* `EllipticPdes.NormedDivForm.graphTransfer`: `W1pGraph 2 μ Ω ≃L H1Graph (μ.map L) (L '' Ω)`.
* `EllipticPdes.NormedDivForm.graphTransfer_mem_W12`: it sends `W^{1,2}(Ω)` into `W^{1,2}(L '' Ω)`.
* `EllipticPdes.NormedDivForm.FullEllipticOp.form`: the bilinear form on the graph space.
* `EllipticPdes.NormedDivForm.FullEllipticOp.form_eq_integral`: its integral formula.
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

variable (μ) in
/-- The change of variables `W1pGraph 2 μ Ω ≃L H1Graph (μ.map L) (L '' Ω)`: the transfer along
`toEuclidean` followed by the Riesz bridge. -/
def graphTransfer (Ω : Set E) : W1pGraph 2 μ Ω ≃L[ℝ] H1Graph (μ.map 𝓛) (𝓛 '' Ω) :=
  (W1pGraph.mapEquiv 𝓛).trans W1pGraph.toH1Graph

variable (Ω : Set E)

/-- On `W₀^{1,2}(Ω)` the graph transfer is `transferEquiv`. -/
lemma coe_transferEquiv (u : W1p0 2 μ Ω) :
    (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) = graphTransfer μ Ω u := rfl

/-- **Graph transfer preserves `W^{1,2}`.** -/
theorem graphTransfer_mem_W12 {U : W1pGraph 2 μ Ω} (hU : U ∈ W1pGraph.W12 μ Ω) :
    graphTransfer μ Ω U ∈ H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) :=
  (W1pGraph.toH1Graph_mem_W12_iff _).2 (W1pGraph.mapL_mem_W12 𝓛 hU)

omit [μ.IsAddHaarMeasure] in
/-- The function part of `graphTransfer U` is `u ∘ L.symm`. -/
lemma fnL_graphTransfer_symm_ae (U : W1pGraph 2 μ Ω) :
    ⇑(H1Graph.fnL (graphTransfer μ Ω U)) =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)]
      ⇑(W1pGraph.fnL U) ∘ 𝓛' :=
  W1pGraph.coeFn_fnL_mapOfMP 𝓛 _ U

omit [μ.IsAddHaarMeasure] in
/-- The function part of `graphTransfer U`, read back through `L`, is `u`. -/
lemma fnL_graphTransfer_ae (U : W1pGraph 2 μ Ω) :
    (fun x => H1Graph.fnL (graphTransfer μ Ω U) (𝓛 x)) =ᵐ[μ.restrict Ω] ⇑(W1pGraph.fnL U) :=
  W1pGraph.Internal.fnL_mapL_comp 𝓛 U

omit [μ.IsAddHaarMeasure] in
/-- The gradient of `graphTransfer U` at `L x` is the Riesz vector of `∇u x ∘ L.symm`. -/
lemma gradL_graphTransfer_ae (U : W1pGraph 2 μ Ω) :
    (fun x => H1Graph.gradL (graphTransfer μ Ω U) (𝓛 x)) =ᵐ[μ.restrict Ω]
      fun x => (InnerProductSpace.toDual ℝ 𝔽).symm
        ((W1pGraph.gradL U x).comp (𝓛' : 𝔽 →L[ℝ] E)) := by
  filter_upwards [(measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp
      (W1pGraph.coeFn_gradL_toH1Graph (W1pGraph.mapL 𝓛 U)),
    W1pGraph.Internal.gradL_mapL_comp 𝓛 U] with x h1 h2
  exact h1.trans (congrArg _ h2)

omit [μ.IsAddHaarMeasure] in
/-- A pointwise relation between the function parts of two graphs is true almost everywhere on
`Ω` exactly when their transfers satisfy it almost everywhere on `L '' Ω`. -/
lemma ae_iff_graphTransfer (U V : W1pGraph 2 μ Ω) (P : ℝ → ℝ → Prop) :
    (∀ᵐ x ∂μ.restrict Ω, P (W1pGraph.fnL U x) (W1pGraph.fnL V x)) ↔
      ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω),
        P (H1Graph.fnL (graphTransfer μ Ω U) y) (H1Graph.fnL (graphTransfer μ Ω V) y) := by
  constructor
  · intro h
    filter_upwards [fnL_graphTransfer_symm_ae Ω U, fnL_graphTransfer_symm_ae Ω V,
      (measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae h]
      with y h1 h2 h3
    exact Eq.mp (congrArg₂ P h1.symm h2.symm) h3
  · intro h
    filter_upwards [fnL_graphTransfer_ae Ω U, fnL_graphTransfer_ae Ω V,
      (measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae h]
      with x h1 h2 h3
    exact Eq.mp (congrArg₂ P h1 h2) h3

namespace FullEllipticOp

variable (Op : FullEllipticOp μ)

/-- The bilinear form on the graph space, the form of the transferred operator on
`H1Graph (μ.map L) (L '' Ω)` pulled back along `graphTransfer`. -/
def form : W1pGraph 2 μ Ω →L[ℝ] W1pGraph 2 μ Ω →L[ℝ] ℝ :=
  (Op.transfer.form (𝓛 '' Ω)).bilinearComp
    (graphTransfer μ Ω : W1pGraph 2 μ Ω →L[ℝ] _) (graphTransfer μ Ω : W1pGraph 2 μ Ω →L[ℝ] _)

omit [μ.IsAddHaarMeasure] in
/-- The form on the graph space is the form of the transferred operator on the transfers. -/
theorem form_transfer (U V : W1pGraph 2 μ Ω) :
    Op.form Ω U V =
      Op.transfer.form (𝓛 '' Ω) (graphTransfer μ Ω U) (graphTransfer μ Ω V) := rfl

/-- The form against an element of `W₀^{1,2}(Ω)` is the transferred form against its image under
`transferEquiv`. -/
theorem form_coe (U : W1pGraph 2 μ Ω) (w : W1p0 2 μ Ω) :
    Op.form Ω U w = Op.transfer.form (𝓛 '' Ω) (graphTransfer μ Ω U)
      (transferEquiv μ Ω w : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) := rfl

/-- On `W₀^{1,2}(Ω)` the form on the graph space is `formOn`. -/
theorem formOn_eq_form (u v : W1p0 2 μ Ω) : Op.formOn Ω u v = Op.form Ω u v := rfl

omit [μ.IsAddHaarMeasure] in
/-- **Integral formula.** `B[u, v] = ∫_Ω ∇v (a ∇u) + ∇u (b) v + c u v` on the graph space. -/
theorem form_eq_integral (U V : W1pGraph 2 μ Ω) :
    Op.form Ω U V = ∫ x in Ω, ((W1pGraph.gradL V x) (Op.a x (W1pGraph.gradL U x)) +
      (W1pGraph.gradL U x) (Op.b x) * W1pGraph.fnL V x +
        Op.c x * W1pGraph.fnL U x * W1pGraph.fnL V x) ∂μ := by
  rw [form_transfer, transfer_form_eq_integral,
    ← (measurePreserving_restrict_image 𝓛 μ Ω).integral_comp
      (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  refine integral_congr_ae ?_
  filter_upwards [fnL_graphTransfer_ae Ω U, fnL_graphTransfer_ae Ω V,
    gradL_graphTransfer_ae Ω U, gradL_graphTransfer_ae Ω V] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4]
  exact Internal.transfer_integrand Op x _ _ _ _

end FullEllipticOp

end NormedDivForm

end EllipticPdes
