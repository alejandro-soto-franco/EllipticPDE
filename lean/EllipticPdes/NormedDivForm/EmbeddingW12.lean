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
public import EllipticPdes.Extension.GraphOperatorHaar
public import EllipticPdes.NormedDivForm.Maximum

/-!
# Rellich and extension on `W^{1,2}(Ω)` on a normed space

For a bounded open set with `C¹` boundary in a finite-dimensional real normed space with an
additive Haar measure, the embedding `W^{1,2}(Ω) ↪ L²(Ω)` is compact. `graphTransfer` sends
`W^{1,2}(Ω)` into `W^{1,2}` of the Euclidean image, whose boundary is `C¹` by the definition of
`Extension.HasC1BoundaryNormed`, and `H1Graph.embW12G_isCompact_haar` applies there.

## Main declarations

* `EllipticPdes.NormedDivForm.graphTransferW12`
* `EllipticPdes.NormedDivForm.isCompactOperator_fnL_W12`
* `EllipticPdes.NormedDivForm.exists_extW12`: the extension operator on `W^{1,2}(Ω)`.
-/

@[expose] public section

open MeasureTheory Module

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

variable (μ Ω) in
/-- The graph transfer restricted to `W^{1,2}(Ω)`. -/
def graphTransferW12 : W1pGraph.W12 μ Ω →L[ℝ] H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) :=
  ((graphTransfer μ Ω : W1pGraph 2 μ Ω →L[ℝ] H1Graph (μ.map 𝓛) (𝓛 '' Ω)).comp
    (W1pGraph.W12 μ Ω).subtypeL).codRestrict _ fun U => graphTransfer_mem_W12 Ω U.2

/-- **Inverse graph transfer preserves `W^{1,2}`.** -/
theorem graphTransfer_symm_mem_W12 {V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)}
    (hV : V ∈ H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω)) : (graphTransfer μ Ω).symm V ∈ W1pGraph.W12 μ Ω := by
  rw [graphTransfer, ContinuousLinearEquiv.symm_trans_apply]
  exact W1pGraph.mapEquiv_symm_mem_W12 _
    ((W1pGraph.toH1Graph_mem_W12_iff _).1 (by rwa [ContinuousLinearEquiv.apply_symm_apply]))

variable (μ Ω) in
/-- The inverse graph transfer restricted to `W^{1,2}`. -/
def graphTransferW12Symm : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ] W1pGraph.W12 μ Ω :=
  ((graphTransfer μ Ω).symm.toContinuousLinearMap.comp
    (H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω)).subtypeL).codRestrict _ fun V =>
      graphTransfer_symm_mem_W12 V.2

variable (μ Ω) in
/-- **Graph transfer as an equivalence of the `W^{1,2}` spaces.** -/
def graphTransferW12Equiv : W1pGraph.W12 μ Ω ≃L[ℝ] H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) :=
  ContinuousLinearEquiv.equivOfInverse (graphTransferW12 μ Ω) (graphTransferW12Symm μ Ω)
    (fun U => Subtype.ext ((graphTransfer μ Ω).symm_apply_apply (U : W1pGraph 2 μ Ω)))
    (fun V => Subtype.ext ((graphTransfer μ Ω).apply_symm_apply (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω))))

lemma coe_graphTransferW12Equiv (U : W1pGraph.W12 μ Ω) :
    (graphTransferW12Equiv μ Ω U : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) =
      graphTransfer μ Ω (U : W1pGraph 2 μ Ω) := rfl

lemma coe_graphTransferW12Equiv_symm (V : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω)) :
    ((graphTransferW12Equiv μ Ω).symm V : W1pGraph 2 μ Ω) =
      (graphTransfer μ Ω).symm (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)) := rfl

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

/-! ### The extension operator -/

section Extension

/-- The extension on `E` conjugated from an extension on the Euclidean image. -/
def extW12Of (Ext' : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ]
      H1Graph.W12 (μ.map 𝓛) (𝓛 '' (Set.univ : Set E))) :
    W1pGraph.W12 μ Ω →L[ℝ] W1pGraph.W12 μ (Set.univ : Set E) :=
  (graphTransferW12Equiv μ (Set.univ : Set E)).symm.toContinuousLinearMap.comp
    (Ext'.comp (graphTransferW12Equiv μ Ω).toContinuousLinearMap)

/-- The transfer of the extension is the Euclidean extension of the transfer. -/
lemma graphTransfer_extW12Of (Ext' : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ]
      H1Graph.W12 (μ.map 𝓛) (𝓛 '' (Set.univ : Set E)))
    (U : W1pGraph.W12 μ Ω) :
    graphTransfer μ (Set.univ : Set E) (extW12Of Ext' U : W1pGraph 2 μ Set.univ) =
      (Ext' (graphTransferW12Equiv μ Ω U)).1 :=
  (graphTransfer μ (Set.univ : Set E)).apply_symm_apply _

/-- An equality almost everywhere on `univ` is an equality almost everywhere. -/
lemma Internal.ae_eq_of_restrict_univ {α β : Type*} [MeasurableSpace α] {ν : Measure α}
    {f g : α → β} (h : f =ᵐ[ν.restrict Set.univ] g) : f =ᵐ[ν] g := by
  rwa [Measure.restrict_univ] at h

/-- The function part of the extension, read through `L`. -/
lemma fnL_extW12Of_ae (Ext' : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ]
      H1Graph.W12 (μ.map 𝓛) (𝓛 '' (Set.univ : Set E)))
    (U : W1pGraph.W12 μ Ω) :
    (fun x => H1Graph.fnL (Ext' (graphTransferW12Equiv μ Ω U)).1 (𝓛 x)) =ᵐ[μ]
      ⇑(W1pGraph.fnL (extW12Of Ext' U : W1pGraph 2 μ Set.univ)) :=
  Internal.ae_eq_of_restrict_univ (by
    simpa only [graphTransfer_extW12Of Ext'] using
      fnL_graphTransfer_ae Set.univ (extW12Of Ext' U : W1pGraph 2 μ Set.univ))

/-- The gradient part of the extension, read through `L`. -/
lemma gradL_extW12Of_ae (Ext' : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ]
      H1Graph.W12 (μ.map 𝓛) (𝓛 '' (Set.univ : Set E)))
    (U : W1pGraph.W12 μ Ω) :
    (fun x => H1Graph.gradL (Ext' (graphTransferW12Equiv μ Ω U)).1 (𝓛 x)) =ᵐ[μ]
      fun x => (InnerProductSpace.toDual ℝ 𝔽).symm
        ((W1pGraph.gradL (extW12Of Ext' U : W1pGraph 2 μ Set.univ) x).comp
          (𝓛' : 𝔽 →L[ℝ] E)) :=
  Internal.ae_eq_of_restrict_univ (by
    simpa only [graphTransfer_extW12Of Ext'] using
      gradL_graphTransfer_ae Set.univ (extW12Of Ext' U : W1pGraph 2 μ Set.univ))

/-- The extension on `E` built from an extension on the Euclidean image. -/
theorem Internal.exists_extW12_of (Ext' : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω) →L[ℝ]
      H1Graph.W12 (μ.map 𝓛) (𝓛 '' (Set.univ : Set E)))
    {O : Set E} (C : ℝ)
    (hagree : ∀ V : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω),
      ⇑(H1Graph.fnL (Ext' V).1) =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] ⇑(H1Graph.fnL V.1) ∧
      ⇑(H1Graph.gradL (Ext' V).1) =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] ⇑(H1Graph.gradL V.1))
    (hsupp : ∀ V : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω), ∀ᵐ z ∂(μ.map 𝓛), z ∉ 𝓛 '' O →
      H1Graph.fnL (Ext' V).1 z = 0)
    (hnorm : ∀ V : H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω), ‖Ext' V‖ ≤ C * ‖V‖) :
    ∃ (Ext : W1pGraph.W12 μ Ω →L[ℝ] W1pGraph.W12 μ (Set.univ : Set E)) (C' : ℝ),
      (∀ U : W1pGraph.W12 μ Ω,
        ⇑(W1pGraph.fnL (Ext U : W1pGraph 2 μ Set.univ)) =ᵐ[μ.restrict Ω]
          ⇑(W1pGraph.fnL (U : W1pGraph 2 μ Ω)) ∧
        ⇑(W1pGraph.gradL (Ext U : W1pGraph 2 μ Set.univ)) =ᵐ[μ.restrict Ω]
          ⇑(W1pGraph.gradL (U : W1pGraph 2 μ Ω))) ∧
      (∀ U : W1pGraph.W12 μ Ω, ∀ᵐ y ∂μ, y ∉ O →
        W1pGraph.fnL (Ext U : W1pGraph 2 μ Set.univ) y = 0) ∧
      ∀ U : W1pGraph.W12 μ Ω, ‖Ext U‖ ≤ C' * ‖U‖ := by
  refine ⟨extW12Of Ext',
    ‖(graphTransferW12Equiv μ (Set.univ : Set E)).symm.toContinuousLinearMap‖ * max C 0 *
      ‖(graphTransferW12Equiv μ Ω).toContinuousLinearMap‖,
    fun U => ⟨?_, ?_⟩, fun U => ?_, fun U => ?_⟩
  · filter_upwards [ae_restrict_of_ae ((fnL_extW12Of_ae Ext' U).symm),
      (measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp (hagree _).1,
      fnL_graphTransfer_ae Ω (U : W1pGraph 2 μ Ω)] with x h1 h2 h3
    exact h1.trans (h2.trans h3)
  · filter_upwards [ae_restrict_of_ae (gradL_extW12Of_ae Ext' U),
      (measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp (hagree _).2,
      gradL_graphTransfer_ae Ω (U : W1pGraph 2 μ Ω)] with x h1 h2 h3
    exact Internal.riesz_comp_injective (h1.symm.trans (h2.trans h3))
  · filter_upwards [fnL_extW12Of_ae Ext' U, (show MeasurePreserving 𝓛 μ (μ.map 𝓛) from
      ⟨(toEuclidean (E := E)).continuous.measurable, rfl⟩).quasiMeasurePreserving.ae
        (hsupp (graphTransferW12Equiv μ Ω U))] with y h1 h2 hy
    rw [← h1]
    exact h2 fun h => hy ((toEuclidean (E := E)).injective.mem_set_image.1 h)
  · calc ‖extW12Of Ext' U‖
        ≤ ‖(graphTransferW12Equiv μ (Set.univ : Set E)).symm.toContinuousLinearMap‖ *
          ‖Ext' (graphTransferW12Equiv μ Ω U)‖ :=
          (graphTransferW12Equiv μ (Set.univ : Set E)).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖(graphTransferW12Equiv μ (Set.univ : Set E)).symm.toContinuousLinearMap‖ *
          (max C 0 * (‖(graphTransferW12Equiv μ Ω).toContinuousLinearMap‖ * ‖U‖)) := by
          gcongr
          exact (hnorm _).trans (mul_le_mul (le_max_left _ _)
            ((graphTransferW12Equiv μ Ω).toContinuousLinearMap.le_opNorm U) (norm_nonneg _)
            (le_max_right _ _))
      _ = _ := by ring

end Extension

/-- **Extension operator on a normed space** (Evans §5.4 Theorem 1 at `p = 2`). On a bounded
open set with `C¹` boundary in a finite-dimensional real normed space of positive dimension with
an additive Haar measure, and for any open set containing its closure, there is a bounded linear
map from `W^{1,2}(Ω)` to `W^{1,2}(E)` that agrees with each element on `Ω`, in the function and in
the gradient, and whose function part vanishes almost everywhere outside the open set. -/
theorem exists_extW12 (hd : 0 < finrank ℝ E) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : Extension.HasC1BoundaryNormed Ω) {O : Set E} (hO : IsOpen O)
    (hsub : closure Ω ⊆ O) :
    ∃ (Ext : W1pGraph.W12 μ Ω →L[ℝ] W1pGraph.W12 μ (Set.univ : Set E)) (C : ℝ),
      (∀ U : W1pGraph.W12 μ Ω,
        ⇑(W1pGraph.fnL (Ext U : W1pGraph 2 μ Set.univ)) =ᵐ[μ.restrict Ω]
          ⇑(W1pGraph.fnL (U : W1pGraph 2 μ Ω)) ∧
        ⇑(W1pGraph.gradL (Ext U : W1pGraph 2 μ Set.univ)) =ᵐ[μ.restrict Ω]
          ⇑(W1pGraph.gradL (U : W1pGraph 2 μ Ω))) ∧
      (∀ U : W1pGraph.W12 μ Ω, ∀ᵐ y ∂μ, y ∉ O →
        W1pGraph.fnL (Ext U : W1pGraph 2 μ Set.univ) y = 0) ∧
      ∀ U : W1pGraph.W12 μ Ω, ‖Ext U‖ ≤ C * ‖U‖ :=
  (H1Graph.exists_extW12G_haar hd (μ.map 𝓛)
    (show IsOpen (𝓛 '' Ω) from (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩo)
    (isBounded_toEuclidean_image hΩb) hC1
    (show IsOpen (𝓛 '' O) from (toEuclidean (E := E)).toHomeomorph.isOpenMap _ hO)
    (show closure (𝓛 '' Ω) ⊆ 𝓛 '' O by
      rw [← show 𝓛 '' closure Ω = closure (𝓛 '' Ω) from
        (toEuclidean (E := E)).toHomeomorph.image_closure Ω]
      exact Set.image_mono hsub)
    (Set.image_univ_of_surjective (toEuclidean (E := E)).surjective)).elim fun Ext' h =>
      h.elim fun C hC => Internal.exists_extW12_of Ext' C hC.1 hC.2.1 hC.2.2

end NormedDivForm

end EllipticPdes
