/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.SobolevP.Graph

/-!
# `W^{1,2}_0` and `H^1_0` on an inner product space

On a finite-dimensional real inner product space `F` the gradient of `W1pGraph 2 ν Ω` takes values
in `StrongDual ℝ F`, and the gradient of `H1Graph ν Ω` takes values in `F`. The Riesz map
`(toDual ℝ F).symm` identifies the two, and postcomposition with it is an isometry of the `L²`
gradient components.

## Main declarations

* `EllipticPdes.W1pGraph.toH1Graph`: the identity on the function and `g ↦ (toDual ℝ F).symm ∘ g`
  on the gradient, as a continuous linear equivalence `W1pGraph 2 ν Ω ≃L[ℝ] H1Graph ν Ω`.
* `EllipticPdes.W1pGraph.norm_toH1Graph`: the equivalence preserves the norm.
* `EllipticPdes.W1pGraph.toH1Graph_testGraph`: it sends test graphs to test graphs.
* `EllipticPdes.W1p0.toH01`: the induced equivalence `W1p0 2 ν Ω ≃L[ℝ] H1Graph.H01 ν Ω`.
* `EllipticPdes.W1p0.fnL_toH01`, `EllipticPdes.W1p0.gradL_toH01`: the formulas for the two
  components.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] {ν : Measure F} {Ω : Set F}

/-- The Riesz map `StrongDual ℝ F → F` as a real-linear isometry equivalence. -/
def RieszBridge.rieszL : StrongDual ℝ F ≃ₗᵢ[ℝ] F :=
  { (InnerProductSpace.toDual ℝ F).symm with
    map_smul' := fun c x => by simp }

/-- `RieszBridge.rieszL` as a continuous linear map. -/
def RieszBridge.rieszC : StrongDual ℝ F →L[ℝ] F :=
    RieszBridge.rieszL.toContinuousLinearEquiv.toContinuousLinearMap

/-- The inverse of `RieszBridge.rieszL` as a continuous linear map. -/
def RieszBridge.rieszC' : F →L[ℝ] StrongDual ℝ F :=
  RieszBridge.rieszL.symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [MeasurableSpace F] in
lemma RieszBridge.rieszL_apply (ξ : StrongDual ℝ F) :
    RieszBridge.rieszL ξ = (InnerProductSpace.toDual ℝ F).symm ξ := rfl

lemma RieszBridge.norm_compLp_rieszL (g : Lp (StrongDual ℝ F) 2 (ν.restrict Ω)) :
    ‖RieszBridge.rieszC.compLp g‖ = ‖g‖ := by
  have h : ∀ᵐ x ∂(ν.restrict Ω), ‖(RieszBridge.rieszC.compLp g : F → F) x‖ = ‖g x‖ := by
    filter_upwards [ContinuousLinearMap.coeFn_compLp RieszBridge.rieszC g] with x hx
    rw [hx]
    exact RieszBridge.rieszL.norm_map _
  rw [Lp.norm_def, Lp.norm_def, 
    eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) h]

namespace W1pGraph

/-- The gradient component of the forward map. -/
def RieszBridge.gradFwd : Lp (StrongDual ℝ F) 2 (ν.restrict Ω) →L[ℝ] Lp F 2 (ν.restrict Ω) :=
  RieszBridge.rieszC.compLpL 2 (ν.restrict Ω)

/-- The gradient component of the backward map. -/
def RieszBridge.gradBwd : Lp F 2 (ν.restrict Ω) →L[ℝ] Lp (StrongDual ℝ F) 2 (ν.restrict Ω) :=
  RieszBridge.rieszC'.compLpL 2 (ν.restrict Ω)

/-- The forward map: identity on the function, Riesz postcomposition on the gradient. -/
def RieszBridge.toH1GraphFwd : W1pGraph 2 ν Ω →L[ℝ] H1Graph ν Ω :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (ν.restrict Ω))
    (Lp F 2 (ν.restrict Ω))).symm.toContinuousLinearMap.comp
    ((fnL (p := 2) (μ := ν) (Ω := Ω)).prod (RieszBridge.gradFwd.comp (gradL (p := 2) (μ := ν) (Ω
    := Ω))))

/-- The backward map: identity on the function, inverse Riesz postcomposition on the gradient. -/
def RieszBridge.toH1GraphBwd : H1Graph ν Ω →L[ℝ] W1pGraph 2 ν Ω :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (ν.restrict Ω))
    (Lp (StrongDual ℝ F) 2 (ν.restrict Ω))).symm.toContinuousLinearMap.comp
    ((H1Graph.fnL (μ := ν) (Ω := Ω)).prod (RieszBridge.gradBwd.comp (H1Graph.gradL (μ := ν) (Ω :=
    Ω))))

lemma RieszBridge.coeFn_gradL_toH1GraphFwd (U : W1pGraph 2 ν Ω) :
    ⇑(H1Graph.gradL (RieszBridge.toH1GraphFwd U)) =ᵐ[ν.restrict Ω]
      fun x => (InnerProductSpace.toDual ℝ F).symm (gradL U x) :=
  ContinuousLinearMap.coeFn_compLp
    RieszBridge.rieszC (gradL U)

lemma RieszBridge.coeFn_gradL_toH1GraphBwd (U : H1Graph ν Ω) :
    ⇑(gradL (RieszBridge.toH1GraphBwd U)) =ᵐ[ν.restrict Ω]
      fun x => InnerProductSpace.toDual ℝ F (H1Graph.gradL U x) :=
  ContinuousLinearMap.coeFn_compLp
    RieszBridge.rieszC' (H1Graph.gradL U)

lemma RieszBridge.toH1GraphBwd_Fwd (U : W1pGraph 2 ν Ω) : RieszBridge.toH1GraphBwd
    (RieszBridge.toH1GraphFwd U) = U := by
  refine WithLp.ofLp_injective 2 (Prod.ext rfl ?_)
  refine Lp.ext ?_
  filter_upwards [RieszBridge.coeFn_gradL_toH1GraphBwd (RieszBridge.toH1GraphFwd U),
    RieszBridge.coeFn_gradL_toH1GraphFwd U] with x a c
  change ⇑(gradL (RieszBridge.toH1GraphBwd (RieszBridge.toH1GraphFwd U))) x = _
  rw [a]
  change InnerProductSpace.toDual ℝ F (H1Graph.gradL (RieszBridge.toH1GraphFwd U) x) = _
  rw [c]
  simp
  rfl

lemma RieszBridge.toH1GraphFwd_Bwd (U : H1Graph ν Ω) : RieszBridge.toH1GraphFwd
    (RieszBridge.toH1GraphBwd U) = U := by
  refine WithLp.ofLp_injective 2 (Prod.ext rfl ?_)
  refine Lp.ext ?_
  filter_upwards [RieszBridge.coeFn_gradL_toH1GraphFwd (RieszBridge.toH1GraphBwd U),
    RieszBridge.coeFn_gradL_toH1GraphBwd U] with x a c
  change ⇑(H1Graph.gradL (RieszBridge.toH1GraphFwd (RieszBridge.toH1GraphBwd U))) x = _
  rw [a]
  rw [c]
  simp
  rfl

/-- **Riesz bridge on graph spaces.** The identity on the function and `g ↦ (toDual ℝ F).symm
∘ g` on the gradient give a continuous linear equivalence from `W1pGraph 2 ν Ω` to `H1Graph ν Ω`. -/
def toH1Graph : W1pGraph 2 ν Ω ≃L[ℝ] H1Graph ν Ω :=
  ContinuousLinearEquiv.equivOfInverse RieszBridge.toH1GraphFwd RieszBridge.toH1GraphBwd
      RieszBridge.toH1GraphBwd_Fwd
    RieszBridge.toH1GraphFwd_Bwd

@[simp] lemma toH1Graph_apply (U : W1pGraph 2 ν Ω) : toH1Graph (ν := ν) U =
    RieszBridge.toH1GraphFwd U := rfl

@[simp] lemma toH1Graph_symm_apply (U : H1Graph ν Ω) :
    (toH1Graph (ν := ν) (Ω := Ω)).symm U = RieszBridge.toH1GraphBwd U := rfl

/-- The function part of `toH1Graph U` is the function part of `U`. -/
lemma fnL_toH1Graph (U : W1pGraph 2 ν Ω) : H1Graph.fnL (toH1Graph U) = fnL U := rfl

/-- The gradient part of `toH1Graph U` is the Riesz image of the gradient part of `U`. -/
lemma coeFn_gradL_toH1Graph (U : W1pGraph 2 ν Ω) :
    ⇑(H1Graph.gradL (toH1Graph U)) =ᵐ[ν.restrict Ω]
      fun x => (InnerProductSpace.toDual ℝ F).symm (gradL U x) :=
  RieszBridge.coeFn_gradL_toH1GraphFwd U

/-- The Riesz bridge preserves the `ℓ²` product norm. -/
theorem norm_toH1Graph (U : W1pGraph 2 ν Ω) : ‖toH1Graph U‖ = ‖U‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  have h : ‖(H1Graph.gradL (toH1Graph U))‖ = ‖gradL U‖ := RieszBridge.norm_compLp_rieszL _
  have h' : ‖(H1Graph.fnL (toH1Graph U))‖ = ‖fnL U‖ := rfl
  exact congrArg₂ (fun a b => Real.sqrt (a ^ 2 + b ^ 2)) h' h

variable [BorelSpace F] [IsFiniteMeasureOnCompacts ν]

/-- The Riesz bridge sends the `W1pGraph` test graph of `φ` to the `H1Graph` test graph of `φ`. -/
theorem toH1Graph_testGraph (φ : testFunctionsNormed Ω) :
    toH1Graph (testGraph (p := 2) (μ := ν) φ) = H1Graph.testGraphₗ ν Ω φ := by
  refine H1Graph.ext ?_ ?_
  · rfl
  · refine Lp.ext ?_
    filter_upwards [coeFn_gradL_toH1Graph (testGraph (p := 2) (μ := ν) φ),
      coeFn_gradL_testGraphₗ (p := 2) (μ := ν) φ,
      H1Graph.coeFn_gradL_testGraphₗ (μ := ν) (Ω := Ω) φ] with x a b c
    rw [a, b, c]
    rfl

end W1pGraph

namespace W1p0

variable [BorelSpace F] [IsFiniteMeasureOnCompacts ν]

lemma RieszBridge.toH1Graph_mem {U : W1pGraph 2 ν Ω} (hU : U ∈ W1p0 2 ν Ω) :
    W1pGraph.toH1Graph U ∈ H1Graph.H01 ν Ω := by
  have hcl : IsClosed ((W1pGraph.toH1Graph (ν := ν) (Ω := Ω)) ⁻¹'
      (H1Graph.H01 ν Ω : Set (H1Graph ν Ω))) :=
    (H1Graph.isClosed_H01).preimage (W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).continuous
  have hsub : (LinearMap.range (W1pGraph.testGraphₗ 2 ν Ω) : Set (W1pGraph 2 ν Ω)) ⊆
      (W1pGraph.toH1Graph (ν := ν) (Ω := Ω)) ⁻¹' (H1Graph.H01 ν Ω : Set (H1Graph ν Ω)) := by
    rintro _ ⟨φ, rfl⟩
    change (W1pGraph.toH1Graph (ν := ν) (Ω := Ω)) (W1pGraph.testGraphₗ 2 ν Ω φ) ∈
      (H1Graph.H01 ν Ω : Set (H1Graph ν Ω))
    rw [W1pGraph.toH1Graph_testGraph φ]
    exact H1Graph.testGraphₗ_mem_H01 φ
  rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hU
  exact closure_minimal hsub hcl hU

lemma RieszBridge.toH1Graph_symm_mem {U : H1Graph ν Ω} (hU : U ∈ H1Graph.H01 ν Ω) :
    (W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).symm U ∈ W1p0 2 ν Ω := by
  have hcl : IsClosed (((W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).symm) ⁻¹'
      (W1p0 2 ν Ω : Set (W1pGraph 2 ν Ω))) :=
    (isClosed_W1p0 2 ν Ω).preimage (W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).symm.continuous
  refine H1Graph.H01_subset_of_isClosed hcl (fun φ => ?_) hU
  refine (Submodule.le_topologicalClosure _) ⟨φ, ?_⟩
  rw [ContinuousLinearEquiv.eq_symm_apply]
  exact W1pGraph.toH1Graph_testGraph φ

/-- The Riesz bridge restricted to `W1p0`. -/
def RieszBridge.toH01Fwd : W1p0 2 ν Ω →L[ℝ] H1Graph.H01 ν Ω :=
  ((W1pGraph.toH1Graph : W1pGraph 2 ν Ω ≃L[ℝ] H1Graph ν Ω).toContinuousLinearMap.comp
    (W1p0 2 ν Ω).subtypeL).codRestrict (H1Graph.H01 ν Ω) (fun U => RieszBridge.toH1Graph_mem U.2)

/-- The inverse Riesz bridge restricted to `H01`. -/
def RieszBridge.toH01Bwd : H1Graph.H01 ν Ω →L[ℝ] W1p0 2 ν Ω :=
  ((W1pGraph.toH1Graph : W1pGraph 2 ν Ω ≃L[ℝ] H1Graph ν Ω).symm.toContinuousLinearMap.comp
    (H1Graph.H01 ν Ω).subtypeL).codRestrict (W1p0 2 ν Ω) (fun U => RieszBridge.toH1Graph_symm_mem
    U.2)

lemma RieszBridge.toH01Bwd_Fwd (U : W1p0 2 ν Ω) : RieszBridge.toH01Bwd (RieszBridge.toH01Fwd U) =
    U :=
  Subtype.ext ((W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).symm_apply_apply (U : W1pGraph 2 ν Ω))

lemma RieszBridge.toH01Fwd_Bwd (U : H1Graph.H01 ν Ω) : RieszBridge.toH01Fwd (RieszBridge.toH01Bwd
    U) = U :=
  Subtype.ext ((W1pGraph.toH1Graph (ν := ν) (Ω := Ω)).apply_symm_apply (U : H1Graph ν Ω))

/-- **`W^{1,2}_0 = H^1_0`.** The Riesz bridge restricts to a continuous linear equivalence from
`W1p0 2 ν Ω` to `H1Graph.H01 ν Ω`. -/
def toH01 : W1p0 2 ν Ω ≃L[ℝ] H1Graph.H01 ν Ω :=
  ContinuousLinearEquiv.equivOfInverse RieszBridge.toH01Fwd RieszBridge.toH01Bwd
      RieszBridge.toH01Bwd_Fwd RieszBridge.toH01Fwd_Bwd

lemma coe_toH01 (U : W1p0 2 ν Ω) :
    (toH01 U : H1Graph ν Ω) = W1pGraph.toH1Graph (U : W1pGraph 2 ν Ω) := rfl

/-- The function part of `toH01 u` is that of `u`. -/
theorem fnL_toH01 (u : W1p0 2 ν Ω) : H1Graph.fnL (toH01 u : H1Graph ν Ω) = fnL u := rfl

/-- The gradient part of `toH01 u` is the Riesz image of that of `u`. -/
theorem gradL_toH01 (u : W1p0 2 ν Ω) :
    ⇑(H1Graph.gradL (toH01 u : H1Graph ν Ω)) =ᵐ[ν.restrict Ω]
      fun x => (InnerProductSpace.toDual ℝ F).symm (gradL u x) :=
  W1pGraph.coeFn_gradL_toH1Graph (u : W1pGraph 2 ν Ω)

end W1p0

end EllipticPdes
