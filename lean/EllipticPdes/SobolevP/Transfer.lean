/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.SobolevP.Graph

/-!
# Change of variables on `W^{1,p}`

A continuous linear equivalence `L : E ≃L[ℝ] F` of finite-dimensional real normed spaces sends
`W1pGraph p μ Ω` to `W1pGraph p (μ.map L) (L '' Ω)`. The function part is `u ↦ u ∘ L.symm` and
the gradient part is `g ↦ fun y => (g (L.symm y)).comp L.symm`. The map sends test graphs to test
graphs, so it restricts to a continuous linear equivalence of the `W1p0` spaces.

## Main declarations

* `EllipticPdes.map_restrict_image`: `(μ.restrict Ω).map L = (μ.map L).restrict (L '' Ω)`.
* `EllipticPdes.W1pGraph.mapL`: the change of variables on graph spaces.
* `EllipticPdes.W1pGraph.mapL_testGraph`: it sends the test graph of `φ` to that of `φ ∘ L.symm`.
* `EllipticPdes.W1p0.mapEquiv`: the induced equivalence of `W1p0` spaces.
* `EllipticPdes.W1p0.fnL_mapEquiv`, `EllipticPdes.W1p0.gradL_mapEquiv`: the formulas for the two
  components.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EllipticPdes

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]

section Measure

variable [BorelSpace E] [BorelSpace F]

/-- **Image of a restricted measure.** Pushing `μ.restrict Ω` forward along a continuous linear
equivalence gives the pushforward of `μ` restricted to the image of `Ω`. -/
theorem map_restrict_image (L : E ≃L[ℝ] F) (μ : Measure E) (Ω : Set E) :
    (μ.restrict Ω).map L = (μ.map L).restrict (L '' Ω) := by
  have h := L.toHomeomorph.toMeasurableEquiv.restrict_map μ (L '' Ω)
  change (μ.map L).restrict (L '' Ω) = (μ.restrict (L ⁻¹' (L '' Ω))).map L at h
  rw [L.injective.preimage_image] at h
  exact h.symm

/-- A continuous linear equivalence is measure-preserving from `μ.restrict Ω` to the restriction
of the pushforward to the image. -/
theorem measurePreserving_restrict_image (L : E ≃L[ℝ] F) (μ : Measure E) (Ω : Set E) :
    MeasurePreserving L (μ.restrict Ω) ((μ.map L).restrict (L '' Ω)) :=
  ⟨L.continuous.measurable, map_restrict_image L μ Ω⟩

/-- The inverse of a continuous linear equivalence is measure-preserving from the restriction of
the pushforward to the image to `μ.restrict Ω`. -/
theorem measurePreserving_symm_restrict_image (L : E ≃L[ℝ] F) (μ : Measure E) (Ω : Set E) :
    MeasurePreserving L.symm ((μ.map L).restrict (L '' Ω)) (μ.restrict Ω) := by
  have h := (measurePreserving_restrict_image L μ Ω)
  have h' : MeasurePreserving L.toHomeomorph.toMeasurableEquiv (μ.restrict Ω)
      ((μ.map L).restrict (L '' Ω)) := h
  exact h'.symm L.toHomeomorph.toMeasurableEquiv

/-- The pushforward of a measure finite on compacts along a continuous linear equivalence is
finite on compacts. -/
instance (L : E ≃L[ℝ] F) (μ : Measure E) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (μ.map L) :=
  Measure.IsFiniteMeasureOnCompacts.map μ L.toHomeomorph

end Measure

namespace W1pGraph

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} {Ω : Set E} {μ' : Measure F} {Ω' : Set F}

/-- The pull-back of covectors along `L.symm`, `ξ ↦ ξ ∘ L.symm`. -/
def dualMap (L : E ≃L[ℝ] F) : StrongDual ℝ E →L[ℝ] StrongDual ℝ F :=
  (ContinuousLinearMap.compL ℝ F E ℝ).flip (L.symm : F →L[ℝ] E)

omit [MeasurableSpace E] [MeasurableSpace F] in
@[simp] lemma dualMap_apply (L : E ≃L[ℝ] F) (ξ : StrongDual ℝ E) (y : F) :
    dualMap L ξ y = ξ (L.symm y) := rfl

/-- The change of variables on graph spaces, for any target measure and set for which `L.symm`
is measure-preserving. -/
def mapOfMP (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) :
    W1pGraph p μ Ω →L[ℝ] W1pGraph p μ' Ω' :=
  (WithLp.prodContinuousLinearEquiv p ℝ (Lp ℝ p (μ'.restrict Ω'))
    (Lp (StrongDual ℝ F) p (μ'.restrict Ω'))).symm.toContinuousLinearMap.comp
    (((Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := p) L.symm h).toContinuousLinearMap.comp
        fnL).prod
      (((dualMap L).compLpL p (μ'.restrict Ω')).comp
        ((Lp.compMeasurePreservingₗᵢ ℝ (E := StrongDual ℝ E) (p := p) L.symm
          h).toContinuousLinearMap.comp gradL)))

lemma fnL_mapOfMP (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) (U : W1pGraph p μ Ω) :
    fnL (mapOfMP L h U) = Lp.compMeasurePreserving L.symm h (fnL U) := rfl

lemma coeFn_fnL_mapOfMP (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) (U : W1pGraph p μ Ω) :
    ⇑(fnL (mapOfMP L h U)) =ᵐ[μ'.restrict Ω'] ⇑(fnL U) ∘ L.symm :=
  Lp.coeFn_compMeasurePreserving _ h

lemma coeFn_gradL_mapOfMP (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) (U : W1pGraph p μ Ω) :
    ⇑(gradL (mapOfMP L h U)) =ᵐ[μ'.restrict Ω']
      fun y => dualMap L (gradL U (L.symm y)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (dualMap L) (p := p) (μ := μ'.restrict Ω')
    (Lp.compMeasurePreserving L.symm h (gradL U))
  have h2 := Lp.coeFn_compMeasurePreserving (gradL U) h
  filter_upwards [h1, h2] with y a b
  exact a.trans (congrArg _ b)

/-- The change of variables for `L.symm` undoes the one for `L`. -/
lemma mapOfMP_comp (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω))
    (h' : MeasurePreserving L.symm.symm (μ.restrict Ω) (μ'.restrict Ω')) (U : W1pGraph p μ Ω) :
    mapOfMP (p := p) L.symm h' (mapOfMP L h U) = U := by
  have hf : fnL (mapOfMP (p := p) L.symm h' (mapOfMP L h U)) = fnL U := by
    refine Lp.ext ?_
    have h1 := coeFn_fnL_mapOfMP L.symm h' (mapOfMP L h U)
    have h2 := h'.quasiMeasurePreserving.ae_eq_comp (coeFn_fnL_mapOfMP L h U)
    filter_upwards [h1, h2] with x a b
    exact a.trans (b.trans (by simp))
  have hg : gradL (mapOfMP (p := p) L.symm h' (mapOfMP L h U)) = gradL U := by
    refine Lp.ext ?_
    have h1 := coeFn_gradL_mapOfMP L.symm h' (mapOfMP L h U)
    have h2 := h'.quasiMeasurePreserving.ae_eq_comp (coeFn_gradL_mapOfMP L h U)
    filter_upwards [h1, h2] with x a b
    have b' : ⇑(gradL (mapOfMP L h U)) (L.symm.symm x) =
        dualMap L (gradL U (L.symm (L x))) := b
    rw [a, b']
    ext v
    simp
  exact WithLp.ofLp_injective p (Prod.ext hf hg)

omit [MeasurableSpace E] [MeasurableSpace F] in
/-- Precomposition with `L.symm` sends a test function on `Ω` to a test function on any `Ω'`
that contains `L '' Ω`. -/
lemma comp_symm_mem_testFunctionsNormed (L : E ≃L[ℝ] F) (hΩ : L '' Ω ⊆ Ω')
    {φ : E → ℝ} (h : φ ∈ testFunctionsNormed Ω) :
    φ ∘ L.symm ∈ testFunctionsNormed Ω' := by
  refine ⟨h.1.comp L.symm.contDiff, h.2.1.comp_homeomorph L.symm.toHomeomorph, ?_⟩
  refine (closure_mono (Function.support_comp_eq_preimage φ L.symm).subset).trans ?_
  refine (L.symm.continuous.closure_preimage_subset _).trans ?_
  intro y hy
  exact hΩ ⟨L.symm y, h.2.2 hy, by simp⟩

variable [BorelSpace E] [BorelSpace F]

/-- The change of variables on `W^{1,p}` graph spaces. The function part is `u ↦ u ∘ L.symm` and
the gradient part is `g ↦ fun y => (g (L.symm y)).comp L.symm`. -/
def mapL (L : E ≃L[ℝ] F) : W1pGraph p μ Ω →L[ℝ] W1pGraph p (μ.map L) (L '' Ω) :=
  mapOfMP L (measurePreserving_symm_restrict_image L μ Ω)

section TestGraph

variable [IsFiniteMeasureOnCompacts μ]
  [IsFiniteMeasureOnCompacts μ']

/-- The change of variables sends the test graph of `φ` to the test graph of `φ ∘ L.symm`. -/
lemma mapOfMP_testGraph (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) (hΩ : L '' Ω ⊆ Ω')
    (φ : testFunctionsNormed Ω) :
    mapOfMP L h (testGraph (p := p) (μ := μ) φ) =
      testGraph (p := p) (μ := μ') ⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩ := by
  have hf : fnL (mapOfMP L h (testGraph (p := p) (μ := μ) φ)) = fnL (testGraph (p := p) (μ := μ')
      (⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩ : testFunctionsNormed Ω')) := by
    refine Lp.ext ?_
    filter_upwards [coeFn_fnL_mapOfMP L h (testGraph (p := p) (μ := μ) φ),
      h.quasiMeasurePreserving.ae_eq_comp (coeFn_fnL_testGraphₗ (p := p) (μ := μ) φ),
      coeFn_fnL_testGraphₗ (p := p) (μ := μ')
        (⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩ : testFunctionsNormed Ω')]
      with y a b c
    exact a.trans (b.trans c.symm)
  have hg : gradL (mapOfMP L h (testGraph (p := p) (μ := μ) φ)) = gradL (testGraph (p := p)
      (μ := μ') (⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩ :
        testFunctionsNormed Ω')) := by
    refine Lp.ext ?_
    filter_upwards [coeFn_gradL_mapOfMP L h (testGraph (p := p) (μ := μ) φ),
      h.quasiMeasurePreserving.ae_eq_comp (coeFn_gradL_testGraphₗ (p := p) (μ := μ) φ),
      coeFn_gradL_testGraphₗ (p := p) (μ := μ')
        (⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩ : testFunctionsNormed Ω')]
      with y a b c
    have b' : ⇑(gradL (testGraph (p := p) (μ := μ) φ)) (L.symm y) =
        fderiv ℝ (φ : E → ℝ) (L.symm y) := b
    rw [a, b', c]
    have hd : DifferentiableAt ℝ (φ : E → ℝ) (L.symm y) :=
      φ.2.1.differentiable (by simp) _
    change _ = fderiv ℝ ((φ : E → ℝ) ∘ L.symm) y
    rw [fderiv_comp y (by simpa using hd) L.symm.differentiableAt, L.symm.fderiv]
    rfl
  exact WithLp.ofLp_injective p (Prod.ext hf hg)

/-- The test graph of `φ` goes to the test graph of `φ ∘ L.symm`. -/
lemma mapL_testGraph (L : E ≃L[ℝ] F) (φ : testFunctionsNormed Ω) :
    mapL (p := p) (μ := μ) L (testGraph φ) =
      testGraph ⟨φ ∘ L.symm, comp_symm_mem_testFunctionsNormed L subset_rfl φ.2⟩ :=
  mapOfMP_testGraph L _ subset_rfl φ

end TestGraph

end W1pGraph

namespace W1p0

variable [BorelSpace E] [BorelSpace F] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} {Ω : Set E}
  {μ' : Measure F} {Ω' : Set F} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts μ']

/-- The change of variables sends `W1p0` into `W1p0`, because it sends test graphs to test
graphs and is continuous. -/
lemma Transfer.mapOfMP_mem (L : E ≃L[ℝ] F)
    (h : MeasurePreserving L.symm (μ'.restrict Ω') (μ.restrict Ω)) (hΩ : L '' Ω ⊆ Ω')
    {U : W1pGraph p μ Ω} (hU : U ∈ W1p0 p μ Ω) : W1pGraph.mapOfMP L h U ∈ W1p0 p μ' Ω' := by
  have hcl : IsClosed (W1pGraph.mapOfMP L h ⁻¹' (W1p0 p μ' Ω' : Set (W1pGraph p μ' Ω'))) :=
    (isClosed_W1p0 p μ' Ω').preimage (W1pGraph.mapOfMP L h).continuous
  have hsub : (LinearMap.range (W1pGraph.testGraphₗ p μ Ω) : Set (W1pGraph p μ Ω)) ⊆
      W1pGraph.mapOfMP L h ⁻¹' (W1p0 p μ' Ω' : Set (W1pGraph p μ' Ω')) := by
    rintro _ ⟨φ, rfl⟩
    exact (Submodule.le_topologicalClosure _)
      ⟨⟨_, W1pGraph.comp_symm_mem_testFunctionsNormed L hΩ φ.2⟩,
        (W1pGraph.mapOfMP_testGraph (p := p) (μ := μ) (μ' := μ') L h hΩ φ).symm⟩
  rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hU
  exact closure_minimal hsub hcl hU

/-- The forward change of variables, as a map `W₀^{1,p}(Ω) → W₀^{1,p}(L '' Ω)`. -/
def Transfer.mapFwd (L : E ≃L[ℝ] F) : W1p0 p μ Ω →L[ℝ] W1p0 p (μ.map L) (L '' Ω) :=
  ((W1pGraph.mapL (p := p) (μ := μ) (Ω := Ω) L).comp (W1p0 p μ Ω).subtypeL).codRestrict
    (W1p0 p (μ.map L) (L '' Ω))
    (fun U => Transfer.mapOfMP_mem (μ' := μ.map L) L (measurePreserving_symm_restrict_image L μ Ω)
      subset_rfl U.2)

/-- The inverse change of variables, as a map `W₀^{1,p}(L '' Ω) → W₀^{1,p}(Ω)`. -/
def Transfer.mapBwd (L : E ≃L[ℝ] F) : W1p0 p (μ.map L) (L '' Ω) →L[ℝ] W1p0 p μ Ω :=
  ((W1pGraph.mapOfMP (p := p) (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
      (measurePreserving_restrict_image L μ Ω)).comp
    (W1p0 p (μ.map L) (L '' Ω)).subtypeL).codRestrict (W1p0 p μ Ω)
    (fun U => Transfer.mapOfMP_mem (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
      (measurePreserving_restrict_image L μ Ω)
      (by rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩; simpa using hx) U.2)

lemma Transfer.coe_mapFwd (L : E ≃L[ℝ] F) (U : W1p0 p μ Ω) :
    (Transfer.mapFwd L U : W1pGraph p (μ.map L) (L '' Ω)) = W1pGraph.mapL L (U : W1pGraph p μ Ω)
    := rfl

lemma Transfer.coe_mapBwd (L : E ≃L[ℝ] F) (U : W1p0 p (μ.map L) (L '' Ω)) :
    (Transfer.mapBwd L U : W1pGraph p μ Ω) =
      W1pGraph.mapOfMP (p := p) (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
        (measurePreserving_restrict_image L μ Ω) (U : W1pGraph p (μ.map L) (L '' Ω)) := rfl

lemma Transfer.mapBwd_mapFwd (L : E ≃L[ℝ] F) (U : W1p0 p μ Ω) : Transfer.mapBwd L
    (Transfer.mapFwd L U) = U := by
  refine Subtype.ext ?_
  rw [Transfer.coe_mapBwd, Transfer.coe_mapFwd]
  exact W1pGraph.mapOfMP_comp L (measurePreserving_symm_restrict_image L μ Ω)
    (measurePreserving_restrict_image L μ Ω) _

lemma Transfer.mapFwd_mapBwd (L : E ≃L[ℝ] F) (U : W1p0 p (μ.map L) (L '' Ω)) :
    Transfer.mapFwd L (Transfer.mapBwd L U) = U := by
  refine Subtype.ext ?_
  rw [Transfer.coe_mapFwd, Transfer.coe_mapBwd]
  exact W1pGraph.mapOfMP_comp (μ := μ.map L) (Ω := L '' Ω) (μ' := μ) (Ω' := Ω) L.symm
    (measurePreserving_restrict_image L μ Ω) (measurePreserving_symm_restrict_image L μ Ω) _

/-- **Change of variables on `W₀^{1,p}`.** A continuous linear equivalence `L` induces a
continuous linear equivalence `W₀^{1,p}(Ω) ≃L W₀^{1,p}(L '' Ω)`, with respect to the pushforward
measure. -/
def mapEquiv (L : E ≃L[ℝ] F) :
    W1p0 p μ Ω ≃L[ℝ] W1p0 p (μ.map L) (L '' Ω) :=
  ContinuousLinearEquiv.equivOfInverse (Transfer.mapFwd L) (Transfer.mapBwd L)
      (Transfer.mapBwd_mapFwd L)
    (Transfer.mapFwd_mapBwd L)

/-- The function part of `mapEquiv L U` is `u ∘ L.symm`. -/
theorem fnL_mapEquiv (L : E ≃L[ℝ] F) (U : W1p0 p μ Ω) :
    ⇑(fnL (mapEquiv L U)) =ᵐ[(μ.map L).restrict (L '' Ω)] ⇑(fnL U) ∘ L.symm :=
  W1pGraph.coeFn_fnL_mapOfMP L _ (U : W1pGraph p μ Ω)

/-- The gradient part of `mapEquiv L U` is `fun y => (g (L.symm y)).comp L.symm`. -/
theorem gradL_mapEquiv (L : E ≃L[ℝ] F) (U : W1p0 p μ Ω) :
    ⇑(gradL (mapEquiv L U)) =ᵐ[(μ.map L).restrict (L '' Ω)]
      fun y => (gradL U (L.symm y)).comp (L.symm : F →L[ℝ] E) :=
  W1pGraph.coeFn_gradL_mapOfMP L _ (U : W1pGraph p μ Ω)

end W1p0

end EllipticPdes
