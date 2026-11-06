/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.InteriorSmooth
public import EllipticPdes.Poincare.GraphBounded
public import EllipticPdes.Embedding.H01SobolevHaar

/-!
# Embedding theorems on a normed space

On a finite-dimensional real normed space with an additive Haar measure `μ`, the embedding
`W₀^{1,2}(Ω) ↪ L²(Ω)` is compact for a bounded measurable `Ω`. The Poincaré inequality holds on a
bounded `Ω`, and in dimension at least two the Sobolev inequality bounds `‖u‖_q` for some `q > 2`.
Each comes from its inner-product twin by transfer along `toEuclidean`. The function part of
`transferEquiv u` is `u ∘ L.symm`, which has the same `L^q` seminorms, and the gradient part is the
Riesz vector of `∇u ∘ L.symm`, whose norm is at most `‖L.symm‖ ‖∇u‖` pointwise.

## Main declarations

* `EllipticPdes.NormedDivForm.isCompactOperator_fnL`
* `EllipticPdes.NormedDivForm.poincare_W1p0_of_bounded`
* `EllipticPdes.NormedDivForm.exists_eLpNorm_le_of_mem_W1p0`: the Sobolev inequality, from
  `H1Graph.exists_eLpNorm_le_of_mem_H01_haar`.
-/

@[expose] public section

open MeasureTheory Module
open scoped NNReal

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

/-- The function part of `u` is the inverse transfer of the function part of `transferEquiv u`. -/
lemma fnL_eq_transferLp_symm (u : W1p0 2 μ Ω) :
    W1p0.fnL u = (transferLp μ Ω).symm (H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω u)) :=
  ((transferLp μ Ω).symm_apply_eq.2 (embL2_transferEquiv Ω u).symm).symm

/-- **Rellich on a normed space.** For a bounded measurable set `Ω` in a finite-dimensional real
normed space with an additive Haar measure, the embedding `W₀^{1,2}(Ω) ↪ L²(Ω)` is compact. -/
theorem isCompactOperator_fnL (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    IsCompactOperator (W1p0.fnL : W1p0 2 μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω)) := by
  convert ((H1Graph.embL2_isCompact_haar (μ.map 𝓛) (measurableSet_toEuclidean_image hΩm)
      (isBounded_toEuclidean_image hΩb)).clm_comp
        (transferLp μ Ω).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp_clm
      (transferEquiv μ Ω).toContinuousLinearMap using 1
  exact funext fun u => fnL_eq_transferLp_symm u

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The Riesz vector of `ξ ∘ L.symm` has norm at most `‖L.symm‖ ‖ξ‖`. -/
lemma Internal.norm_riesz_comp_le [FiniteDimensional ℝ E] (ξ : StrongDual ℝ E) :
    ‖(InnerProductSpace.toDual ℝ 𝔽).symm (ξ.comp (𝓛' : 𝔽 →L[ℝ] E))‖ ≤
      ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖ξ‖ :=
  ((InnerProductSpace.toDual ℝ 𝔽).symm.norm_map _).trans_le
    ((ξ.opNorm_comp_le _).trans_eq (mul_comm _ _))

/-- The `L²` norm of the gradient part grows by at most `‖L.symm‖` under the transfer. -/
lemma norm_gradL_transferEquiv_le (u : W1p0 2 μ Ω) :
    ‖H1Graph.gradL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω))‖ ≤
      ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1p0.gradL u‖ := by
  rw [← Lp.norm_compMeasurePreserving _ (measurePreserving_restrict_image 𝓛 μ Ω)]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (H1Graph.gradL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))
      (measurePreserving_restrict_image 𝓛 μ Ω), gradL_transferEquiv_ae Ω u] with x h1 h2
  rw [h1, Function.comp_apply, h2]
  exact Internal.norm_riesz_comp_le _

/-- **Poincaré inequality on a normed space.** On a bounded set of a nontrivial
finite-dimensional real normed space with an additive Haar measure, `‖u‖² ≤ C ‖∇u‖²` for every
`u ∈ W₀^{1,2}(Ω)`. -/
theorem poincare_W1p0_of_bounded [Nontrivial E] (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p0 2 μ Ω, ‖W1p0.fnL u‖ ^ 2 ≤ C * ‖W1p0.gradL u‖ ^ 2 := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  obtain ⟨C, hC, h⟩ := H1Graph.poincare_H01_of_bounded (μ := μ.map 𝓛)
    (isBounded_toEuclidean_image hΩb)
  exact ⟨C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ ^ 2, by positivity, fun u =>
    calc ‖W1p0.fnL u‖ ^ 2
        = ‖H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω))‖ ^ 2 := by
          rw [← norm_embL2_transferEquiv Ω u]; rfl
      _ ≤ C * ‖H1Graph.gradL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω))‖ ^ 2 :=
          h _ (transferEquiv μ Ω u).2
      _ ≤ C * (‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1p0.gradL u‖) ^ 2 := by
          gcongr; exact norm_gradL_transferEquiv_le u
      _ = C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ ^ 2 * ‖W1p0.gradL u‖ ^ 2 := by ring⟩

/-- The `L^q` seminorm of the function part is preserved by the transfer. -/
lemma eLpNorm_fnL_transferEquiv (q : ℝ≥0) (u : W1p0 2 μ Ω) :
    eLpNorm (⇑(W1p0.fnL u)) q (μ.restrict Ω) = eLpNorm
      (⇑(H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))) q
      ((μ.map 𝓛).restrict (𝓛 '' Ω)) :=
  (eLpNorm_congr_ae (fnL_transferEquiv_ae Ω u).symm).trans
    (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable _)
      (measurePreserving_restrict_image 𝓛 μ Ω))

/-- One instance of the transferred Sobolev inequality. -/
lemma Internal.eLpNorm_le_transfer {q : ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ V : H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω),
      MemLp (⇑(H1Graph.fnL (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))) q ((μ.map 𝓛).restrict (𝓛 '' Ω)) ∧
        (eLpNorm (⇑(H1Graph.fnL (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))) q
          ((μ.map 𝓛).restrict (𝓛 '' Ω))).toReal ≤
            C * ‖H1Graph.gradL (V : H1Graph (μ.map 𝓛) (𝓛 '' Ω))‖)
    (u : W1p0 2 μ Ω) :
    MemLp (⇑(W1p0.fnL u)) q (μ.restrict Ω) ∧
      (eLpNorm (⇑(W1p0.fnL u)) q (μ.restrict Ω)).toReal ≤
        C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1p0.gradL u‖ := by
  refine ⟨((h (transferEquiv μ Ω u)).1.comp_measurePreserving
    (measurePreserving_restrict_image 𝓛 μ Ω)).ae_eq (fnL_transferEquiv_ae Ω u), ?_⟩
  calc (eLpNorm (⇑(W1p0.fnL u)) q (μ.restrict Ω)).toReal
      = (eLpNorm (⇑(H1Graph.fnL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))) q
          ((μ.map 𝓛).restrict (𝓛 '' Ω))).toReal := by rw [eLpNorm_fnL_transferEquiv]
    _ ≤ C * ‖H1Graph.gradL (transferEquiv μ Ω u : H1Graph (μ.map 𝓛) (𝓛 '' Ω))‖ :=
        (h (transferEquiv μ Ω u)).2
    _ ≤ C * (‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1p0.gradL u‖) := by
        gcongr; exact norm_gradL_transferEquiv_le u
    _ = C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖ * ‖W1p0.gradL u‖ := by ring

/-- **Sobolev inequality on a normed space.** In dimension at least two, on a bounded measurable
set of a finite-dimensional real normed space with an additive Haar measure, `W₀^{1,2}(Ω)` embeds
into `L^q(Ω)` for some `q > 2`, with `‖u‖_q ≤ C ‖∇u‖₂`. -/
theorem exists_eLpNorm_le_of_mem_W1p0 (hn : 2 ≤ finrank ℝ E) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p0 2 μ Ω,
      MemLp (⇑(W1p0.fnL u)) q (μ.restrict Ω) ∧
        (eLpNorm (⇑(W1p0.fnL u)) q (μ.restrict Ω)).toReal ≤ C * ‖W1p0.gradL u‖ := by
  obtain ⟨q, hq, C, hC, h⟩ := H1Graph.exists_eLpNorm_le_of_mem_H01_haar (μ.map 𝓛)
    (by simpa using hn) (measurableSet_toEuclidean_image hΩm) (isBounded_toEuclidean_image hΩb)
  exact ⟨q, hq, C * ‖(𝓛' : 𝔽 →L[ℝ] E)‖, by positivity, Internal.eLpNorm_le_transfer hC h⟩

end NormedDivForm

end EllipticPdes
