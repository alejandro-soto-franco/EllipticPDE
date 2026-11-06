/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.EmbeddingW12
public import EllipticPdes.Spectrum.PoincareWirtingerHaar

/-!
# Poincaré's inequality with the mean subtracted on a normed space

On a finite-dimensional real normed space with an additive Haar measure `μ`, for a bounded,
connected, open domain with `C¹` boundary, one constant bounds the `L²` distance of every element of
`W^{1,2}(Ω)` from its mean by the `L²` norm of its gradient. `graphTransfer` sends `W^{1,2}(Ω)` into
`W^{1,2}` of the Euclidean image, where `H1Graph.Internal.exists_const_le_haar` gives a class
almost everywhere equal to a constant within `C ‖∇v‖` of the image. The inverse of `transferLp` is
an isometry and takes that class to a class almost everywhere equal to the same constant, and the
gradient norm grows by at most `‖L.symm‖` under the transfer. `L2Mean.norm_sub_mean_le_of_exists`
then puts the mean in place of the constant.

## Main declarations

* `EllipticPdes.NormedDivForm.norm_gradL_graphTransfer_le`
* `EllipticPdes.NormedDivForm.poincare_wirtinger`
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

omit [μ.IsAddHaarMeasure] in
/-- The `L²` norm of the gradient part grows by at most `‖L.symm‖` under the graph transfer. -/
lemma norm_gradL_graphTransfer_le (U : W1pGraph 2 μ Ω) :
    ‖H1Graph.gradL (graphTransfer μ Ω U)‖ ≤ ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1pGraph.gradL U‖ := by
  rw [← Lp.norm_compMeasurePreserving _ (measurePreserving_restrict_image 𝓛 μ Ω)]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (H1Graph.gradL (graphTransfer μ Ω U))
      (measurePreserving_restrict_image 𝓛 μ Ω), gradL_graphTransfer_ae Ω U] with x h1 h2
  rw [h1, Function.comp_apply, h2]
  exact Internal.norm_riesz_comp_le _

omit [μ.IsAddHaarMeasure] in
/-- The inverse transfer of `g`, read through `L.symm`, is almost everywhere constant when `g`
is. -/
lemma Internal.coeFn_transferLp_symm_comp {g : Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω))} {a : ℝ}
    (ha : ⇑g =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun _ => a) :
    (⇑((transferLp μ Ω).symm g) ∘ 𝓛') =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun _ => a := by
  refine (Lp.coeFn_compMeasurePreserving _ (measurePreserving_symm_restrict_image 𝓛 μ Ω)).symm.trans
    ?_
  rw [← transferLp_apply, LinearIsometryEquiv.apply_symm_apply]
  exact ha

omit [μ.IsAddHaarMeasure] in
/-- **The inverse transfer sends constants to constants.** -/
lemma Internal.transferLp_symm_ae {g : Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω))} {a : ℝ}
    (ha : ⇑g =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun _ => a) :
    ⇑((transferLp μ Ω).symm g) =ᵐ[μ.restrict Ω] fun _ => a := by
  filter_upwards [(measurePreserving_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp
    (Internal.coeFn_transferLp_symm_comp ha)] with x hx
  simpa using hx

omit [μ.IsAddHaarMeasure] in
/-- One instance of the transferred inequality, in the form with a constant class. -/
lemma Internal.exists_const_le_transfer_of {C : ℝ} (hC : 0 ≤ C) {U : W1pGraph 2 μ Ω}
    {g : Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω))}
    (hg : (∃ a : ℝ, ⇑g =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun _ => a) ∧
      ‖H1Graph.fnL (graphTransfer μ Ω U) - g‖ ≤ C * ‖H1Graph.gradL (graphTransfer μ Ω U)‖) :
    ∃ g' : Lp ℝ 2 (μ.restrict Ω), (∃ a : ℝ, ⇑g' =ᵐ[μ.restrict Ω] fun _ => a) ∧
      ‖W1pGraph.fnL U - g'‖ ≤ C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1pGraph.gradL U‖ :=
  ⟨(transferLp μ Ω).symm g, hg.1.elim fun a ha => ⟨a, Internal.transferLp_symm_ae ha⟩,
    calc ‖W1pGraph.fnL U - (transferLp μ Ω).symm g‖
        = ‖(transferLp μ Ω).symm (H1Graph.fnL (graphTransfer μ Ω U) - g)‖ := by
          rw [map_sub, ← fnL_eq_transferLp_symm_graph]
      _ = ‖H1Graph.fnL (graphTransfer μ Ω U) - g‖ := LinearIsometryEquiv.norm_map _ _
      _ ≤ C * ‖H1Graph.gradL (graphTransfer μ Ω U)‖ := hg.2
      _ ≤ C * (‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1pGraph.gradL U‖) :=
          mul_le_mul_of_nonneg_left (norm_gradL_graphTransfer_le U) hC
      _ = C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1pGraph.gradL U‖ := (mul_assoc _ _ _).symm⟩

/-- The transferred inequality, in the form with a constant class. -/
lemma Internal.exists_const_le_transfer {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ V ∈ H1Graph.W12 (μ.map 𝓛) (𝓛 '' Ω), ∃ g : Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω)),
      (∃ a : ℝ, ⇑g =ᵐ[(μ.map 𝓛).restrict (𝓛 '' Ω)] fun _ => a) ∧
        ‖H1Graph.fnL V - g‖ ≤ C * ‖H1Graph.gradL V‖)
    {U : W1pGraph 2 μ Ω} (hU : U ∈ W1pGraph.W12 μ Ω) :
    ∃ g : Lp ℝ 2 (μ.restrict Ω), (∃ a : ℝ, ⇑g =ᵐ[μ.restrict Ω] fun _ => a) ∧
      ‖W1pGraph.fnL U - g‖ ≤ C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1pGraph.gradL U‖ :=
  (h _ (graphTransfer_mem_W12 Ω hU)).elim fun _ hg => Internal.exists_const_le_transfer_of hC hg

/-- **Poincaré's inequality with the mean subtracted on a normed space** (Evans §5.8.1 Theorem 1
at `p = 2`). On a bounded, connected, open domain with `C¹` boundary in a finite-dimensional real
normed space of positive dimension with an additive Haar measure, one constant bounds the `L²`
distance of every element of `W^{1,2}(Ω)` from its mean by the `L²` norm of its gradient. The
finiteness of `μ.restrict Ω` follows from boundedness and is taken as an instance. -/
theorem poincare_wirtinger [IsFiniteMeasure (μ.restrict Ω)] (hd : 0 < finrank ℝ E)
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1BoundaryNormed Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ∈ W1pGraph.W12 μ Ω,
      ‖W1pGraph.fnL U - L2Mean.mean (μ.restrict Ω) (W1pGraph.fnL U) • L2Mean.one (μ.restrict Ω)‖
        ≤ C * ‖W1pGraph.gradL U‖ :=
  (H1Graph.Internal.exists_const_le_haar hd (μ.map 𝓛)
      ((toEuclidean (E := E)).toHomeomorph.isOpenMap _ hΩo) (isBounded_toEuclidean_image hΩb)
      hC1 (hconn.image _ (toEuclidean (E := E)).continuous.continuousOn)
      (hne.image _)).elim fun C hC =>
    ⟨C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖, mul_nonneg hC.1 (norm_nonneg _), fun _ hU =>
      L2Mean.norm_sub_mean_le_of_exists (Internal.exists_const_le_transfer hC.1 hC.2 hU)⟩

end NormedDivForm

end EllipticPdes
