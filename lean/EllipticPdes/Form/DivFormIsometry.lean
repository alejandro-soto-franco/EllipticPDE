/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.DivForm
public import EllipticPdes.Sobolev.GraphIsometry

/-!
# Transport of divergence-form operators along a linear isometry

A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` preserves the canonical volume, so an operator
`Op : FullEllipticOp (volume : Measure E)` has a transported operator on `E'` with coefficients
`y ↦ e ∘ a (e.symm y) ∘ e.symm`, `y ↦ e (b (e.symm y))` and `y ↦ c (e.symm y)`. The forms
correspond under the graph transport `H1Graph.mapIsometry`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.mapIsometry`: the transported operator.
* `EllipticPdes.DivForm.FullEllipticOp.form_mapIsometry`: the full forms correspond.
* `EllipticPdes.DivForm.FullEllipticOp.formOn_mapH01`: the forms on `H₀¹` correspond.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

namespace H1Graph

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

/-- Integrals over `e.symm ⁻¹' Ω` of a function composed with `e.symm` are integrals over `Ω`. -/
lemma integral_comp_symm (e : E ≃ₗᵢ[ℝ] E') (Ω : Set E) (G : E → ℝ) :
    ∫ y in e.symm ⁻¹' Ω, G (e.symm y) = ∫ x in Ω, G x :=
  (measurePreserving_symm_restrict e Ω).integral_comp e.symm.toHomeomorph.measurableEmbedding G

/-- The transported function part of a graph class is the transported function. -/
lemma coeFn_fnL_mapIsometry (e : E ≃ₗᵢ[ℝ] E') (Ω : Set E) (U : H1Graph volume Ω) :
    ⇑(fnL (mapIsometry e Ω U)) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)] fun y => fnL U (e.symm y) :=
  coeFn_pullFn e Ω (fnL U)

/-- The transported gradient part of a graph class is the transported gradient. -/
lemma coeFn_gradL_mapIsometry (e : E ≃ₗᵢ[ℝ] E') (Ω : Set E) (U : H1Graph volume Ω) :
    ⇑(gradL (mapIsometry e Ω U)) =ᵐ[volume.restrict (e.symm ⁻¹' Ω)]
      fun y => e (gradL U (e.symm y)) :=
  coeFn_pullGrad e Ω (gradL U)

/-- The transport commutes with the embedding of `H₀¹` into `L²`. -/
@[simp] lemma embL2_mapH01 (e : E ≃ₗᵢ[ℝ] E') (Ω : Set E) (U : H01 volume Ω) :
    embL2 volume (e.symm ⁻¹' Ω) (mapH01 e Ω U) = pullFn e Ω (embL2 volume Ω U) := rfl

end H1Graph

namespace DivForm

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

/-- Conjugation of an endomorphism by a linear isometry equivalence: `T ↦ e ∘ T ∘ e.symm`. -/
def conjIso (e : E ≃ₗᵢ[ℝ] E') (T : E →L[ℝ] E) : E' →L[ℝ] E' :=
  (e.toContinuousLinearEquiv : E →L[ℝ] E').comp
    (T.comp (e.symm.toContinuousLinearEquiv : E' →L[ℝ] E))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] in
/-- The conjugated endomorphism acts by `y ↦ e (T (e.symm y))`. -/
@[simp] lemma conjIso_apply (e : E ≃ₗᵢ[ℝ] E') (T : E →L[ℝ] E) (y : E') :
    conjIso e T y = e (T (e.symm y)) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] in
/-- Conjugation by a linear isometry equivalence does not increase the operator norm. -/
lemma norm_conjIso_le (e : E ≃ₗᵢ[ℝ] E') (T : E →L[ℝ] E) : ‖conjIso e T‖ ≤ ‖T‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => by
    rw [conjIso_apply, LinearIsometryEquiv.norm_map]
    calc ‖T (e.symm y)‖ ≤ ‖T‖ * ‖e.symm y‖ := T.le_opNorm _
      _ = ‖T‖ * ‖y‖ := by rw [LinearIsometryEquiv.norm_map]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E'] in
/-- Conjugation by a linear isometry equivalence is continuous. -/
lemma continuous_conjIso (e : E ≃ₗᵢ[ℝ] E') : Continuous (conjIso e) :=
  continuous_const.clm_comp (continuous_id.clm_comp continuous_const)

/-- **Transport of an operator along a linear isometry.** The coefficients are
`y ↦ e ∘ a (e.symm y) ∘ e.symm`, `y ↦ e (b (e.symm y))` and `y ↦ c (e.symm y)`, with the same
constants. -/
def FullEllipticOp.mapIsometry (e : E ≃ₗᵢ[ℝ] E') (Op : FullEllipticOp (volume : Measure E)) :
    FullEllipticOp (volume : Measure E') where
  a y := conjIso e (Op.a (e.symm y))
  lam := Op.lam
  Λ := Op.Λ
  lam_pos := Op.lam_pos
  Λ_nonneg := Op.Λ_nonneg
  aestronglyMeasurable :=
    ((continuous_conjIso e).comp_aestronglyMeasurable
      (Op.aestronglyMeasurable.comp_quasiMeasurePreserving
        e.symm.measurePreserving.quasiMeasurePreserving))
  norm_le := by
    filter_upwards [e.symm.measurePreserving.quasiMeasurePreserving.ae Op.norm_le] with y hy
    exact (norm_conjIso_le e _).trans hy
  coercive := by
    filter_upwards [e.symm.measurePreserving.quasiMeasurePreserving.ae Op.coercive] with y hy ξ
    have := hy (e.symm ξ)
    have h : ⟪e ((Op.a (e.symm y)) (e.symm ξ)), ξ⟫ = ⟪(Op.a (e.symm y)) (e.symm ξ), e.symm ξ⟫ := by
      simpa using e.inner_map_map ((Op.a (e.symm y)) (e.symm ξ)) (e.symm ξ)
    rw [conjIso_apply, h]
    simpa using this
  b y := e (Op.b (e.symm y))
  c y := Op.c (e.symm y)
  Bsup := Op.Bsup
  Csup := Op.Csup
  Bsup_nonneg := Op.Bsup_nonneg
  Csup_nonneg := Op.Csup_nonneg
  b_aestronglyMeasurable :=
    e.continuous.comp_aestronglyMeasurable
      (Op.b_aestronglyMeasurable.comp_quasiMeasurePreserving
        e.symm.measurePreserving.quasiMeasurePreserving)
  c_aestronglyMeasurable :=
    Op.c_aestronglyMeasurable.comp_quasiMeasurePreserving
      e.symm.measurePreserving.quasiMeasurePreserving
  norm_b_le := by
    filter_upwards [e.symm.measurePreserving.quasiMeasurePreserving.ae Op.norm_b_le] with y hy
    rwa [LinearIsometryEquiv.norm_map]
  abs_c_le := e.symm.measurePreserving.quasiMeasurePreserving.ae Op.abs_c_le

namespace FullEllipticOp

variable (e : E ≃ₗᵢ[ℝ] E') (Op : FullEllipticOp (volume : Measure E)) (Ω : Set E)

/-- The coefficient field of the transported operator. -/
@[simp] lemma mapIsometry_a (y : E') :
    (Op.mapIsometry e).a y = conjIso e (Op.a (e.symm y)) := rfl

/-- The drift of the transported operator. -/
@[simp] lemma mapIsometry_b (y : E') : (Op.mapIsometry e).b y = e (Op.b (e.symm y)) := rfl

/-- The zeroth-order coefficient of the transported operator. -/
@[simp] lemma mapIsometry_c (y : E') : (Op.mapIsometry e).c y = Op.c (e.symm y) := rfl

/-- **The full forms correspond under the graph transport.** -/
theorem form_mapIsometry (U V : H1Graph volume Ω) :
    (Op.mapIsometry e).form (e.symm ⁻¹' Ω) (H1Graph.mapIsometry e Ω U)
      (H1Graph.mapIsometry e Ω V) = Op.form Ω U V := by
  rw [form_apply, form_apply, EllipticCoeff.form_eq_integral, EllipticCoeff.form_eq_integral,
    lowerForm_eq_integral, lowerForm_eq_integral]
  congr 1
  · rw [← H1Graph.integral_comp_symm e Ω]
    refine integral_congr_ae ?_
    filter_upwards [H1Graph.coeFn_gradL_mapIsometry e Ω U,
      H1Graph.coeFn_gradL_mapIsometry e Ω V] with y h1 h2
    simp only [mapIsometry_a, conjIso_apply, h1, h2, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.inner_map_map]
  · rw [← H1Graph.integral_comp_symm e Ω]
    refine integral_congr_ae ?_
    filter_upwards [H1Graph.coeFn_gradL_mapIsometry e Ω U,
      H1Graph.coeFn_fnL_mapIsometry e Ω U, H1Graph.coeFn_fnL_mapIsometry e Ω V] with y h1 h2 h3
    simp only [mapIsometry_b, mapIsometry_c, h1, h2, h3, LinearIsometryEquiv.inner_map_map]

/-- **The forms on `H₀¹` correspond under the transport `H1Graph.mapH01`.** -/
theorem formOn_mapH01 (U V : H1Graph.H01 volume Ω) :
    (Op.mapIsometry e).formOn (e.symm ⁻¹' Ω) (H1Graph.H01 volume (e.symm ⁻¹' Ω))
      (H1Graph.mapH01 e Ω U) (H1Graph.mapH01 e Ω V) = Op.formOn Ω (H1Graph.H01 volume Ω) U V :=
  form_mapIsometry e Op Ω U V

/-- **A weak solution is transported to a weak solution.** If `u ∈ H₀¹(Ω)` solves `B[u, v] = ⟪f, v⟫`
for every `v ∈ H₀¹(Ω)`, then `mapH01 u` solves the transported problem on `e.symm ⁻¹' Ω` with the
transported datum `pullFn f`. -/
theorem weak_mapH01 (u : H1Graph.H01 volume Ω) (f : Lp ℝ 2 (volume.restrict Ω))
    (h : ∀ v : H1Graph.H01 volume Ω,
      Op.formOn Ω (H1Graph.H01 volume Ω) u v = ⟪f, H1Graph.embL2 volume Ω v⟫)
    (W : H1Graph.H01 volume (e.symm ⁻¹' Ω)) :
    (Op.mapIsometry e).formOn (e.symm ⁻¹' Ω) (H1Graph.H01 volume (e.symm ⁻¹' Ω))
      (H1Graph.mapH01 e Ω u) W =
        ⟪H1Graph.pullFn e Ω f, H1Graph.embL2 volume (e.symm ⁻¹' Ω) W⟫ := by
  set Φ : H1Graph volume (e.symm ⁻¹' Ω) →L[ℝ] ℝ :=
    (Op.mapIsometry e).form (e.symm ⁻¹' Ω) (H1Graph.mapIsometry e Ω u)
      - (innerSL ℝ (H1Graph.pullFn e Ω f)).comp H1Graph.fnL with hΦ
  have hle : H1Graph.H01 volume (e.symm ⁻¹' Ω) ≤ LinearMap.ker (Φ : _ →ₗ[ℝ] ℝ) := by
    refine H1Graph.H01_le_of_isClosed Φ.isClosed_ker fun φ' => ?_
    have hφ : (φ' : E' → ℝ) ∘ e ∈ testFunctions Ω := by
      simpa [Set.preimage_preimage] using comp_mem_testFunctions e.symm φ'.2
    set φ : testFunctions Ω := ⟨(φ' : E' → ℝ) ∘ e, hφ⟩
    have hTG : H1Graph.testGraphₗ volume (e.symm ⁻¹' Ω) φ' =
        H1Graph.mapIsometry e Ω (H1Graph.testGraphₗ volume Ω φ) := by
      rw [H1Graph.mapIsometry_testGraphₗ]
      congr 1
      exact Subtype.ext (by funext y; simp [φ])
    have hmem := H1Graph.testGraphₗ_mem_H01 (μ := volume) φ
    have h1 := h ⟨_, hmem⟩
    rw [formOn_apply] at h1
    rw [LinearMap.mem_ker, hTG]
    change (Op.mapIsometry e).form (e.symm ⁻¹' Ω) (H1Graph.mapIsometry e Ω u)
      (H1Graph.mapIsometry e Ω (H1Graph.testGraphₗ volume Ω φ)) -
        ⟪H1Graph.pullFn e Ω f, H1Graph.fnL (H1Graph.mapIsometry e Ω
          (H1Graph.testGraphₗ volume Ω φ))⟫ = 0
    rw [form_mapIsometry, H1Graph.fnL_mapIsometry, LinearIsometry.inner_map_map, sub_eq_zero]
    exact h1
  have hW := hle W.2
  have : Φ W = 0 := hW
  rw [hΦ] at this
  have h3 := sub_eq_zero.1 (by simpa using this)
  exact h3

end FullEllipticOp

end DivForm

end EllipticPdes
