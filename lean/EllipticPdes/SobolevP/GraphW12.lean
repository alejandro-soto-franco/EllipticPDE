/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.SobolevP.Transfer
public import EllipticPdes.SobolevP.RieszBridge

/-!
# `W^{1,2}(Ω)` on a normed space

The subspace of the graph space `W1pGraph 2 μ Ω` whose gradient part is the weak derivative of
its function part. It is the intersection of the kernels of the continuous functionals
`U ↦ ∫_Ω ∂_v φ u + ∫_Ω φ (g v)`, one for each test function `φ` and direction `v`, and so it is
closed. On a finite-dimensional real inner product space the Riesz bridge identifies it with
`H1Graph.W12`, and a continuous linear equivalence `L` sends it into the space on `L '' Ω`.

## Main declarations

* `EllipticPdes.W1pGraph.W12`: `W^{1,2}(Ω)` in the graph space over a normed space.
* `EllipticPdes.W1pGraph.mem_W12_iff`: membership is the weak derivative identity.
* `EllipticPdes.W1pGraph.W1p0_le_W12`: `W₀^{1,2}(Ω) ⊆ W^{1,2}(Ω)` for a Haar measure.
* `EllipticPdes.W1pGraph.mapEquiv`: the change of variables on the whole graph space.
* `EllipticPdes.W1pGraph.mapL_mem_W12`: the change of variables preserves `W^{1,2}`.
* `EllipticPdes.W1pGraph.toH1Graph_mem_W12_iff`: the Riesz bridge identifies the two `W^{1,2}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace W1pGraph

section Constraint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {Ω : Set E}

/-- A directional derivative of a test function lies in `L²(Ω)`. -/
lemma Internal.memLp_fderiv_apply {φ : E → ℝ} (h : φ ∈ testFunctionsNormed Ω) (v : E) :
    MemLp (fun x => fderiv ℝ φ x v) 2 (μ.restrict Ω) :=
  ((h.1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((h.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun T : StrongDual ℝ E => T v) (by simp))

variable (μ Ω)

/-- The `L²(Ω)` class of `x ↦ fderiv φ x v`. -/
def partialClsN (φ : testFunctionsNormed Ω) (v : E) : Lp ℝ 2 (μ.restrict Ω) :=
  (Internal.memLp_fderiv_apply φ.2 v).toLp fun x => fderiv ℝ (φ : E → ℝ) x v

/-- The `L²(Ω)` class of a test function. -/
def fnClsN (φ : testFunctionsNormed Ω) : Lp ℝ 2 (μ.restrict Ω) :=
  (memLp_of_mem_testFunctionsNormed φ.2).toLp (φ : E → ℝ)

/-- The constraint functional `U ↦ ∫_Ω ∂_v φ u + ∫_Ω φ (g v)`. Its kernel is one instance of the
weak derivative identity. -/
def constraintL (φ : testFunctionsNormed Ω) (v : E) : W1pGraph 2 μ Ω →L[ℝ] ℝ :=
  (innerSL ℝ (partialClsN μ Ω φ v)).comp (fnL (p := 2) (μ := μ) (Ω := Ω)) +
    (innerSL ℝ (fnClsN μ Ω φ)).comp
      (((ContinuousLinearMap.apply ℝ ℝ v).compLpL 2 (μ.restrict Ω)).comp
        (gradL (p := 2) (μ := μ) (Ω := Ω)))

variable {μ Ω}

/-- The constraint functional as two integrals over `Ω`. -/
lemma constraintL_eq_integral (φ : testFunctionsNormed Ω) (v : E) (U : W1pGraph 2 μ Ω) :
    constraintL μ Ω φ v U = ∫ x in Ω, fderiv ℝ (φ : E → ℝ) x v * fnL U x ∂μ +
      ∫ x in Ω, (φ : E → ℝ) x * gradL U x v ∂μ := by
  simp only [constraintL, add_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, L2.inner_def]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [(Internal.memLp_fderiv_apply (μ := μ) φ.2 v).coeFn_toLp] with x hx
    simp only [partialClsN, hx, RCLike.inner_apply, conj_trivial]
    ring
  · refine integral_congr_ae ?_
    filter_upwards [(memLp_of_mem_testFunctionsNormed (μ := μ) (p := 2) φ.2).coeFn_toLp,
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := μ.restrict Ω)
        (ContinuousLinearMap.apply ℝ ℝ v) (gradL U)] with x h1 h2
    simp only [fnClsN, h1, h2, RCLike.inner_apply, conj_trivial,
      ContinuousLinearMap.apply_apply]
    ring

variable (μ Ω)

/-- **`W^{1,2}(Ω)` on a normed space.** The graphs whose gradient part is the weak derivative of
their function part. -/
def W12 : Submodule ℝ (W1pGraph 2 μ Ω) :=
  ⨅ (φ : testFunctionsNormed Ω) (v : E), LinearMap.ker (constraintL μ Ω φ v).toLinearMap

/-- `W^{1,2}(Ω)` as a set is the intersection of the zero sets of the constraint functionals. -/
lemma coe_W12 : (W12 μ Ω : Set (W1pGraph 2 μ Ω)) =
    ⋂ (φ : testFunctionsNormed Ω) (v : E), {U | constraintL μ Ω φ v U = 0} := by
  ext U
  simp [W12]

/-- `W^{1,2}(Ω)` is closed in the graph space. -/
theorem isClosed_W12 : IsClosed (W12 μ Ω : Set (W1pGraph 2 μ Ω)) :=
  coe_W12 μ Ω ▸ isClosed_iInter fun φ => isClosed_iInter fun v =>
    isClosed_eq (constraintL μ Ω φ v).continuous continuous_const

/-- `W^{1,2}(Ω)` is complete. -/
instance : CompleteSpace (W12 μ Ω) := (isClosed_W12 μ Ω).completeSpace_coe

variable {μ Ω}

/-- Membership of `W^{1,2}(Ω)` is the vanishing of every constraint functional. -/
lemma mem_W12_iff_constraintL (U : W1pGraph 2 μ Ω) :
    U ∈ W12 μ Ω ↔ ∀ (φ : testFunctionsNormed Ω) (v : E), constraintL μ Ω φ v U = 0 := by
  simp [W12, Submodule.mem_iInf]

/-- **Membership of `W^{1,2}(Ω)` is the weak derivative identity.** -/
theorem mem_W12_iff (U : W1pGraph 2 μ Ω) :
    U ∈ W12 μ Ω ↔ ∀ (φ : testFunctionsNormed Ω) (v : E),
      ∫ x in Ω, fderiv ℝ (φ : E → ℝ) x v * fnL U x ∂μ +
        ∫ x in Ω, (φ : E → ℝ) x * gradL U x v ∂μ = 0 := by
  simp only [mem_W12_iff_constraintL, constraintL_eq_integral]

end Constraint

section Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

omit [FiniteDimensional ℝ E] in
/-- The first constraint integral of a test graph, over the whole space. -/
lemma Internal.setIntegral_fderiv_mul_fnL_testGraph (φ ψ : testFunctionsNormed Ω) (v : E) :
    ∫ x in Ω, fderiv ℝ (φ : E → ℝ) x v * fnL (testGraph (p := 2) (μ := μ) ψ) x ∂μ =
      ∫ x, fderiv ℝ (φ : E → ℝ) x v * (ψ : E → ℝ) x ∂μ := by
  refine (integral_congr_ae ?_).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_))
  · filter_upwards [coeFn_fnL_testGraphₗ (p := 2) (μ := μ) ψ] with x hx
    rw [hx]
  · rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (φ.2.2.2 h))]
    simp

omit [FiniteDimensional ℝ E] in
/-- The second constraint integral of a test graph, over the whole space. -/
lemma Internal.setIntegral_mul_gradL_testGraph (φ ψ : testFunctionsNormed Ω) (v : E) :
    ∫ x in Ω, (φ : E → ℝ) x * gradL (testGraph (p := 2) (μ := μ) ψ) x v ∂μ =
      ∫ x, (φ : E → ℝ) x * fderiv ℝ (ψ : E → ℝ) x v ∂μ := by
  refine (integral_congr_ae ?_).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_))
  · filter_upwards [coeFn_gradL_testGraphₗ (p := 2) (μ := μ) ψ] with x hx
    rw [hx]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.2.2.2 h)), zero_mul]

/-- Integration by parts for two test functions over the whole space. -/
lemma Internal.integral_fderiv_mul_eq_neg (φ ψ : testFunctionsNormed Ω) (v : E) :
    ∫ x, fderiv ℝ (φ : E → ℝ) x v * (ψ : E → ℝ) x ∂μ =
      -∫ x, (φ : E → ℝ) x * fderiv ℝ (ψ : E → ℝ) x v ∂μ := by
  simpa using ((hasWeakFDerivOn_fderiv (Ω := ⊤) (μ := μ)
    ((ψ.2.1.of_le (by exact_mod_cast le_top)).contDiffOn)) v).integral_eq
    φ.2.1 φ.2.2.1 (by simp)

/-- A test graph lies in `W^{1,2}(Ω)`: integration by parts, with no boundary term by compact
support. -/
theorem testGraph_mem_W12 (ψ : testFunctionsNormed Ω) :
    testGraph (p := 2) (μ := μ) ψ ∈ W12 μ Ω :=
  (mem_W12_iff _).2 fun φ v => by
    rw [Internal.setIntegral_fderiv_mul_fnL_testGraph, Internal.setIntegral_mul_gradL_testGraph,
      Internal.integral_fderiv_mul_eq_neg, neg_add_cancel]

/-- **`W₀^{1,2}(Ω) ⊆ W^{1,2}(Ω)`.** Every element of `W₀^{1,2}(Ω)` has its gradient part as weak
derivative. -/
theorem W1p0_le_W12 : W1p0 2 μ Ω ≤ W12 μ Ω := by
  intro U hU
  rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hU
  refine closure_minimal ?_ (isClosed_W12 μ Ω) hU
  rintro _ ⟨φ, rfl⟩
  exact testGraph_mem_W12 φ

end Haar

section Map

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} {Ω : Set E}

/-- **Change of variables on the graph space.** A continuous linear equivalence `L` induces a
continuous linear equivalence `W1pGraph p μ Ω ≃L W1pGraph p (μ.map L) (L '' Ω)`. -/
def mapEquiv (L : E ≃L[ℝ] F) : W1pGraph p μ Ω ≃L[ℝ] W1pGraph p (μ.map L) (L '' Ω) :=
  ContinuousLinearEquiv.equivOfInverse (mapL L)
    (mapOfMP (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
      (measurePreserving_restrict_image L μ Ω))
    (fun U => mapOfMP_comp L (measurePreserving_symm_restrict_image L μ Ω)
      (measurePreserving_restrict_image L μ Ω) U)
    (fun U => mapOfMP_comp (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
      (measurePreserving_restrict_image L μ Ω) (measurePreserving_symm_restrict_image L μ Ω) U)

@[simp] lemma mapEquiv_apply (L : E ≃L[ℝ] F) (U : W1pGraph p μ Ω) :
    mapEquiv L U = mapL L U := rfl

lemma mapEquiv_symm_apply (L : E ≃L[ℝ] F) (U : W1pGraph p (μ.map L) (L '' Ω)) :
    (mapEquiv (p := p) (μ := μ) (Ω := Ω) L).symm U =
      mapOfMP (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
        (measurePreserving_restrict_image L μ Ω) U := rfl

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Precomposition with `L` sends a test function on `L '' Ω` to a test function on `Ω`. -/
lemma Internal.comp_mem_testFunctionsNormed (L : E ≃L[ℝ] F) (φ : testFunctionsNormed (L '' Ω)) :
    (φ : F → ℝ) ∘ L ∈ testFunctionsNormed Ω := by
  simpa using comp_symm_mem_testFunctionsNormed L.symm
    (by rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx) φ.2

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Chain rule for precomposition with `L`, read in the direction `L.symm w`. -/
lemma Internal.fderiv_comp_apply (L : E ≃L[ℝ] F) {φ : F → ℝ} (hφ : Differentiable ℝ φ)
    (x : E) (w : F) : fderiv ℝ (φ ∘ L) x (L.symm w) = fderiv ℝ φ (L x) w := by
  rw [fderiv_comp x (hφ _) L.differentiableAt, L.fderiv]
  simp

/-- The function part of `mapL L U`, read back through `L`. -/
lemma Internal.fnL_mapL_comp (L : E ≃L[ℝ] F) (U : W1pGraph p μ Ω) :
    (fun x => fnL (mapL L U) (L x)) =ᵐ[μ.restrict Ω] ⇑(fnL U) := by
  filter_upwards [(measurePreserving_restrict_image L μ Ω).quasiMeasurePreserving.ae_eq_comp
    (coeFn_fnL_mapOfMP L (measurePreserving_symm_restrict_image L μ Ω) U)] with x hx
  exact hx.trans (by simp)

/-- The gradient part of `mapL L U`, read back through `L`. -/
lemma Internal.gradL_mapL_comp (L : E ≃L[ℝ] F) (U : W1pGraph p μ Ω) :
    (fun x => gradL (mapL L U) (L x)) =ᵐ[μ.restrict Ω] fun x => dualMap L (gradL U x) := by
  filter_upwards [(measurePreserving_restrict_image L μ Ω).quasiMeasurePreserving.ae_eq_comp
    (coeFn_gradL_mapOfMP L (measurePreserving_symm_restrict_image L μ Ω) U)] with x hx
  exact hx.trans (by simp)

variable [IsFiniteMeasureOnCompacts μ]

/-- The constraint functional of `mapL L U` for `(φ, w)` is the constraint functional of `U` for
`(φ ∘ L, L.symm w)`. -/
lemma Internal.constraintL_mapL (L : E ≃L[ℝ] F) (φ : testFunctionsNormed (L '' Ω)) (w : F)
    (U : W1pGraph 2 μ Ω) :
    constraintL (μ.map L) (L '' Ω) φ w (mapL L U) =
      constraintL μ Ω ⟨_, Internal.comp_mem_testFunctionsNormed L φ⟩ (L.symm w) U := by
  rw [constraintL_eq_integral, constraintL_eq_integral,
    ← (measurePreserving_restrict_image L μ Ω).integral_comp
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
    ← (measurePreserving_restrict_image L μ Ω).integral_comp
      L.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  congr 1 <;> refine integral_congr_ae ?_
  · filter_upwards [Internal.fnL_mapL_comp L U] with x hx
    simp [hx, Internal.fderiv_comp_apply L (φ.2.1.differentiable (by simp))]
  · filter_upwards [Internal.gradL_mapL_comp L U] with x hx
    simp [hx]

/-- **Change of variables preserves `W^{1,2}`.** -/
theorem mapL_mem_W12 (L : E ≃L[ℝ] F) {U : W1pGraph 2 μ Ω} (hU : U ∈ W12 μ Ω) :
    mapL L U ∈ W12 (μ.map L) (L '' Ω) :=
  (mem_W12_iff_constraintL _).2 fun φ w =>
    (Internal.constraintL_mapL L φ w U).trans ((mem_W12_iff_constraintL U).1 hU _ _)

section General

variable {μ' : Measure F} {Ω' : Set F}

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Precomposition with `L` sends a test function on `Ω'` to a test function on `Ω`, once
`L.symm '' Ω' ⊆ Ω`. -/
lemma Internal.comp_mem_testFunctionsNormed_of_subset (L : E ≃L[ℝ] F)
    (hΩ : L.symm '' Ω' ⊆ Ω) (φ : testFunctionsNormed Ω') :
    (φ : F → ℝ) ∘ L ∈ testFunctionsNormed Ω := by
  simpa using comp_symm_mem_testFunctionsNormed L.symm hΩ φ.2

omit [BorelSpace E] [BorelSpace F] [IsFiniteMeasureOnCompacts μ] in
/-- The function part of `mapOfMP L h U`, read back through `L`. -/
lemma Internal.fnL_mapOfMP_comp (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω))
    (h' : MeasurePreserving L (μ.restrict Ω) (μ'.restrict Ω')) (U : W1pGraph p μ Ω) :
    (fun x => fnL (mapOfMP L h U) (L x)) =ᵐ[μ.restrict Ω] ⇑(fnL U) := by
  filter_upwards [h'.quasiMeasurePreserving.ae_eq_comp (coeFn_fnL_mapOfMP L h U)] with x hx
  exact hx.trans (by simp)

omit [BorelSpace E] [BorelSpace F] [IsFiniteMeasureOnCompacts μ] in
/-- The gradient part of `mapOfMP L h U`, read back through `L`. -/
lemma Internal.gradL_mapOfMP_comp (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω))
    (h' : MeasurePreserving L (μ.restrict Ω) (μ'.restrict Ω')) (U : W1pGraph p μ Ω) :
    (fun x => gradL (mapOfMP L h U) (L x)) =ᵐ[μ.restrict Ω] fun x => dualMap L (gradL U x) := by
  filter_upwards [h'.quasiMeasurePreserving.ae_eq_comp (coeFn_gradL_mapOfMP L h U)] with x hx
  exact hx.trans (by simp)

variable [IsFiniteMeasureOnCompacts μ']

/-- The constraint functional of `mapOfMP L h U` for `(φ, w)` is the constraint functional of `U`
for `(φ ∘ L, L.symm w)`. -/
lemma Internal.constraintL_mapOfMP (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω))
    (h' : MeasurePreserving L (μ.restrict Ω) (μ'.restrict Ω')) (hΩ : L.symm '' Ω' ⊆ Ω)
    (φ : testFunctionsNormed Ω') (w : F) (U : W1pGraph 2 μ Ω) :
    constraintL μ' Ω' φ w (mapOfMP L h U) =
      constraintL μ Ω ⟨_, Internal.comp_mem_testFunctionsNormed_of_subset L hΩ φ⟩
        (L.symm w) U := by
  rw [constraintL_eq_integral, constraintL_eq_integral,
    ← h'.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
    ← h'.integral_comp L.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  congr 1 <;> refine integral_congr_ae ?_
  · filter_upwards [Internal.fnL_mapOfMP_comp L h h' U] with x hx
    simp [hx, Internal.fderiv_comp_apply L (φ.2.1.differentiable (by simp))]
  · filter_upwards [Internal.gradL_mapOfMP_comp L h h' U] with x hx
    simp [hx]

/-- **The general change of variables preserves `W^{1,2}`.** -/
theorem mapOfMP_mem_W12 (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω))
    (h' : MeasurePreserving L (μ.restrict Ω) (μ'.restrict Ω')) (hΩ : L.symm '' Ω' ⊆ Ω)
    {U : W1pGraph 2 μ Ω} (hU : U ∈ W12 μ Ω) : mapOfMP L h U ∈ W12 μ' Ω' :=
  (mem_W12_iff_constraintL _).2 fun φ w =>
    (Internal.constraintL_mapOfMP L h h' hΩ φ w U).trans ((mem_W12_iff_constraintL U).1 hU _ _)

/-- **The inverse change of variables preserves `W^{1,2}`.** -/
theorem mapEquiv_symm_mem_W12 (L : E ≃L[ℝ] F)
    {V : W1pGraph 2 (μ.map L) (L '' Ω)} (hV : V ∈ W12 (μ.map L) (L '' Ω)) :
    (mapEquiv L).symm V ∈ W12 μ Ω := by
  rw [mapEquiv_symm_apply]
  exact mapOfMP_mem_W12 L.symm _ (measurePreserving_symm_restrict_image L μ Ω)
    (by rintro _ ⟨y, hy, rfl⟩; simpa using hy) hV

end General

end Map

section Riesz

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {ν : Measure F} [IsFiniteMeasureOnCompacts ν] {Ω : Set F}

/-- The pairing of an `H1Graph` constraint vector with the Riesz image of a graph is the constraint
functional of the graph. -/
lemma inner_constraintVec_toH1Graph (φ : testFunctionsNormed Ω) (v : F) (U : W1pGraph 2 ν Ω) :
    ⟪H1Graph.constraintVec ν Ω ⟨(φ : F → ℝ), φ.2⟩ v, toH1Graph U⟫ = constraintL ν Ω φ v U := by
  rw [H1Graph.inner_constraintVec, constraintL_eq_integral, L2.inner_def, L2.inner_def]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [H1Graph.coeFn_partialCls (μ := ν) ⟨(φ : F → ℝ), φ.2⟩ v] with x hx
    rw [hx, fnL_toH1Graph]
    simp [RCLike.inner_apply, conj_trivial, mul_comm]
  · refine integral_congr_ae ?_
    filter_upwards [H1Graph.coeFn_smulCls (μ := ν) ⟨(φ : F → ℝ), φ.2⟩ v,
      coeFn_gradL_toH1Graph U] with x h1 h2
    rw [h1, h2, real_inner_smul_left, real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- **Riesz bridge between the two `W^{1,2}(Ω)`.** -/
theorem toH1Graph_mem_W12_iff (U : W1pGraph 2 ν Ω) :
    toH1Graph U ∈ H1Graph.W12 ν Ω ↔ U ∈ W12 ν Ω := by
  rw [H1Graph.mem_W12_iff, mem_W12_iff_constraintL]
  exact forall_congr' fun φ => forall_congr' fun v => by
    rw [inner_constraintVec_toH1Graph ⟨(φ : F → ℝ), φ.2⟩ v U]
    rfl

end Riesz

end W1pGraph

end EllipticPdes
