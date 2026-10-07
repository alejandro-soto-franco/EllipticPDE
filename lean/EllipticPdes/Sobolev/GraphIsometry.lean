/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph

/-!
# Linear isometries and the graph space

A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` of finite-dimensional inner product spaces
preserves the canonical volume, so it transports `L²` classes by composition with `e.symm`. On the
graph space this is `U ↦ (fnL U ∘ e.symm, e ∘ gradL U ∘ e.symm)`, a linear isometry from
`H1Graph volume Ω` into `H1Graph volume (e.symm ⁻¹' Ω)`. It sends the graph of a test function
`φ` to the graph of `φ ∘ e.symm`, since `∇(φ ∘ e.symm) y = e (∇φ (e.symm y))`, and therefore maps
`H₀¹(Ω)` into `H₀¹(e.symm ⁻¹' Ω)`.

## Main declarations

* `EllipticPdes.H1Graph.mapIsometry`: the transport `H1Graph volume Ω →ₗᵢ H1Graph volume Ω'`.
* `EllipticPdes.H1Graph.mapIsometry_testGraphₗ`: it sends test graphs to test graphs.
* `EllipticPdes.H1Graph.mapH01`: its restriction `H₀¹(Ω) →L H₀¹(Ω')`.
* `EllipticPdes.H1Graph.pullFn`: the composition `L²(Ω) → L²(Ω')` with `e.symm`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

omit [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ E'] [BorelSpace E']
  [MeasurableSpace E] [MeasurableSpace E'] in
/-- Composition with a smooth linear isometry equivalence preserves test functions, with the
support moved to the preimage. -/
lemma comp_mem_testFunctions (e : E ≃ₗᵢ[ℝ] E') {Ω : Set E} {φ : E → ℝ}
    (h : φ ∈ testFunctions Ω) : (φ ∘ e.symm) ∈ testFunctions (e.symm ⁻¹' Ω) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.comp e.symm.contDiff, h2.comp_isClosedEmbedding
    e.symm.toHomeomorph.isClosedEmbedding, ?_⟩
  exact (tsupport_comp_eq_preimage φ e.symm.toHomeomorph).subset.trans (Set.preimage_mono h3)

omit [BorelSpace E] [BorelSpace E'] [MeasurableSpace E] [MeasurableSpace E'] in
/-- The gradient of `φ ∘ e.symm` is the transported gradient of `φ`. -/
lemma gradient_comp_symm (e : E ≃ₗᵢ[ℝ] E') {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : E') :
    gradient (φ ∘ e.symm) y = e (gradient φ (e.symm y)) := by
  refine ext_inner_left ℝ fun v => ?_
  have hd : DifferentiableAt ℝ φ (e.symm y) :=
    (hφ.differentiable (by simp)).differentiableAt
  have hc : fderiv ℝ (φ ∘ e.symm) y = (fderiv ℝ φ (e.symm y)).comp
      (e.symm.toContinuousLinearEquiv : E' →L[ℝ] E) := by
    rw [fderiv_comp y hd (e.symm.toContinuousLinearEquiv.differentiableAt)]
    congr 1
    exact e.symm.toContinuousLinearEquiv.fderiv
  have hv : ⟪v, e (gradient φ (e.symm y))⟫ = ⟪e.symm v, gradient φ (e.symm y)⟫ := by
    rw [← e.inner_map_map, e.apply_symm_apply]
  rw [inner_gradient_right, hc, hv, inner_gradient_right]
  simp

namespace H1Graph

section Transport

variable (e : E ≃ₗᵢ[ℝ] E') (Ω : Set E)

/-- The inverse isometry pulls the volume on `E'` restricted to `e.symm ⁻¹' Ω` back to the volume
on `E` restricted to `Ω`. -/
lemma measurePreserving_symm_restrict :
    MeasurePreserving e.symm (volume.restrict (e.symm ⁻¹' Ω)) (volume.restrict Ω) :=
  e.symm.measurePreserving.restrict_preimage_emb e.symm.toHomeomorph.measurableEmbedding Ω

/-- The isometry sends the volume on `E` restricted to `Ω` to the volume on `E'` restricted to
`e.symm ⁻¹' Ω`. -/
lemma measurePreserving_restrict :
    MeasurePreserving e (volume.restrict Ω) (volume.restrict (e.symm ⁻¹' Ω)) := by
  have := e.measurePreserving.restrict_preimage_emb e.toHomeomorph.measurableEmbedding
    (e.symm ⁻¹' Ω)
  simpa [Set.preimage_preimage] using this

/-- Composition of `L²(Ω)` classes with `e.symm`, landing in `L²(e.symm ⁻¹' Ω)`. -/
def pullFn : Lp ℝ 2 (volume.restrict Ω) →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict (e.symm ⁻¹' Ω)) :=
  Lp.compMeasurePreservingₗᵢ ℝ e.symm (measurePreserving_symm_restrict e Ω)

/-- Composition of `L²(Ω)` classes with `e`, the inverse of `pullFn`. -/
def pushFn : Lp ℝ 2 (volume.restrict (e.symm ⁻¹' Ω)) →ₗᵢ[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  Lp.compMeasurePreservingₗᵢ ℝ e (measurePreserving_restrict e Ω)

/-- A representative of `pullFn e Ω f` is `f ∘ e.symm` almost everywhere. -/
lemma coeFn_pullFn (f : Lp ℝ 2 (volume.restrict Ω)) :
    ⇑(pullFn e Ω f) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)] f ∘ e.symm :=
  Lp.coeFn_compMeasurePreserving f _

/-- Pushing a pulled class forward returns it. -/
@[simp] lemma pushFn_pullFn (f : Lp ℝ 2 (volume.restrict Ω)) : pushFn e Ω (pullFn e Ω f) = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (pullFn e Ω f) (measurePreserving_restrict e Ω),
    (measurePreserving_restrict e Ω).quasiMeasurePreserving.ae (coeFn_pullFn e Ω f)] with x h1 h2
  change ⇑(Lp.compMeasurePreserving e (measurePreserving_restrict e Ω) (pullFn e Ω f)) x = f x
  exact h1.trans (h2.trans (by simp))

/-- Applying a linear isometry equivalence pointwise to an `L²(ν; E)` class. -/
def pushLp {α : Type*} [MeasurableSpace α] (ν : Measure α) : Lp E 2 ν →ₗᵢ[ℝ] Lp E' 2 ν where
  toLinearMap := ((e.toContinuousLinearEquiv : E →L[ℝ] E').compLpL 2 ν :
    Lp E 2 ν →L[ℝ] Lp E' 2 ν).toLinearMap
  norm_map' g := by
    have h : ∀ᵐ x ∂ν, ‖((e.toContinuousLinearEquiv : E →L[ℝ] E').compLpL 2 ν g) x‖ = ‖g x‖ := by
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := ν)
        (e.toContinuousLinearEquiv : E →L[ℝ] E') g] with x hx
      simp [hx]
    rw [Lp.norm_def, Lp.norm_def]
    exact congrArg ENNReal.toReal
      (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) h)

omit [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ E'] [BorelSpace E']
  [MeasurableSpace E] [MeasurableSpace E'] in
/-- A representative of `pushLp e ν g` is `e ∘ g` almost everywhere. -/
lemma coeFn_pushLp {α : Type*} [MeasurableSpace α] (ν : Measure α) (g : Lp E 2 ν) :
    ⇑(pushLp e ν g) =ᵐ[ν] fun x => e (g x) :=
  ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := ν) (e.toContinuousLinearEquiv : E →L[ℝ] E') g

/-- The gradient part of the transport: `g ↦ e ∘ g ∘ e.symm`. -/
def pullGrad : Lp E 2 (volume.restrict Ω) →ₗᵢ[ℝ] Lp E' 2 (volume.restrict (e.symm ⁻¹' Ω)) :=
  (pushLp e _).comp (Lp.compMeasurePreservingₗᵢ ℝ e.symm (measurePreserving_symm_restrict e Ω))

/-- A representative of `pullGrad e Ω g` is `e ∘ g ∘ e.symm` almost everywhere. -/
lemma coeFn_pullGrad (g : Lp E 2 (volume.restrict Ω)) :
    ⇑(pullGrad e Ω g) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)] fun y => e (g (e.symm y)) := by
  filter_upwards [coeFn_pushLp e _ (Lp.compMeasurePreservingₗᵢ ℝ e.symm
    (measurePreserving_symm_restrict e Ω) g),
    Lp.coeFn_compMeasurePreserving g (measurePreserving_symm_restrict e Ω)] with y h1 h2
  exact h1.trans (congrArg e h2)

/-- **Transport of the graph space.** `U ↦ (fnL U ∘ e.symm, e ∘ gradL U ∘ e.symm)` is a linear
isometry from `H1Graph volume Ω` to `H1Graph volume (e.symm ⁻¹' Ω)`. -/
def mapIsometry : H1Graph volume Ω →ₗᵢ[ℝ] H1Graph volume (e.symm ⁻¹' Ω) where
  toFun U := mk (pullFn e Ω (fnL U)) (pullGrad e Ω (gradL U))
  map_add' U V := by ext <;> simp
  map_smul' c U := by ext <;> simp
  norm_map' U := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq, norm_sq_eq]
    simp

/-- The function part of the transport is `pullFn`. -/
@[simp] lemma fnL_mapIsometry (U : H1Graph volume Ω) :
    fnL (mapIsometry e Ω U) = pullFn e Ω (fnL U) := rfl

/-- The gradient part of the transport is `pullGrad`. -/
@[simp] lemma gradL_mapIsometry (U : H1Graph volume Ω) :
    gradL (mapIsometry e Ω U) = pullGrad e Ω (gradL U) := rfl

/-- The transport sends the graph of `φ` to the graph of `φ ∘ e.symm`. -/
lemma mapIsometry_testGraphₗ (φ : testFunctions Ω) :
    mapIsometry e Ω (testGraphₗ volume Ω φ) =
      testGraphₗ volume (e.symm ⁻¹' Ω) ⟨(φ : E → ℝ) ∘ e.symm, comp_mem_testFunctions e φ.2⟩ := by
  refine ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [coeFn_pullFn e Ω (fnL (testGraphₗ volume Ω φ)),
      (measurePreserving_symm_restrict e Ω).quasiMeasurePreserving.ae (coeFn_fnL_testGraphₗ φ),
      coeFn_fnL_testGraphₗ (μ := volume)
        (⟨(φ : E → ℝ) ∘ e.symm, comp_mem_testFunctions e φ.2⟩ : testFunctions (e.symm ⁻¹' Ω))]
      with y h1 h2 h3
    simp only [fnL_mapIsometry]
    rw [h1, Function.comp_apply, h2, h3]
    rfl
  · filter_upwards [coeFn_pullGrad e Ω (gradL (testGraphₗ volume Ω φ)),
      (measurePreserving_symm_restrict e Ω).quasiMeasurePreserving.ae (coeFn_gradL_testGraphₗ φ),
      coeFn_gradL_testGraphₗ (μ := volume)
        (⟨(φ : E → ℝ) ∘ e.symm, comp_mem_testFunctions e φ.2⟩ : testFunctions (e.symm ⁻¹' Ω))]
      with y h1 h2 h3
    simp only [gradL_mapIsometry]
    rw [h1, h2, h3, gradient_comp_symm e φ.2.1]

/-- The transport maps `H₀¹(Ω)` into `H₀¹(e.symm ⁻¹' Ω)`. -/
lemma mapIsometry_mem_H01 {U : H1Graph volume Ω} (hU : U ∈ H01 volume Ω) :
    mapIsometry e Ω U ∈ H01 volume (e.symm ⁻¹' Ω) := by
  have key : H01 volume Ω ≤ (H01 volume (e.symm ⁻¹' Ω)).comap
      (mapIsometry e Ω).toLinearMap := by
    refine H01_le_of_isClosed ((isClosed_H01).preimage (mapIsometry e Ω).continuous) fun φ => ?_
    change (mapIsometry e Ω (testGraphₗ volume Ω φ) : H1Graph volume (e.symm ⁻¹' Ω)) ∈
      H01 volume (e.symm ⁻¹' Ω)
    rw [mapIsometry_testGraphₗ]
    exact testGraphₗ_mem_H01 _
  exact key hU

/-- The transport restricted to `H₀¹`. -/
def mapH01 : H01 volume Ω →L[ℝ] H01 volume (e.symm ⁻¹' Ω) :=
  ((mapIsometry e Ω).toContinuousLinearMap.comp (H01 volume Ω).subtypeL).codRestrict _
    fun U => mapIsometry_mem_H01 e Ω U.2

/-- `mapH01` is `mapIsometry` on representatives. -/
@[simp] lemma coe_mapH01 (U : H01 volume Ω) :
    (mapH01 e Ω U : H1Graph volume (e.symm ⁻¹' Ω)) = mapIsometry e Ω U := rfl

end Transport

end H1Graph

end EllipticPdes
