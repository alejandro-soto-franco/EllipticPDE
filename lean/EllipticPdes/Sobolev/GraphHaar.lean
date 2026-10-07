/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rescaling the measure of the graph space

The graph space `H1Graph μ Ω` depends on `μ` through the `L²` spaces of `μ.restrict Ω`. For a
positive scalar `c` the identity on representatives is a continuous linear equivalence
`H1Graph (c • μ) Ω ≃L[ℝ] H1Graph μ Ω` (`smulMeasureEquiv`), and it carries the graph of a test
function to the graph of the same test function (`smulMeasureL_testGraphₗ`). Hence it maps
`H₀¹` to `H₀¹`.

An additive Haar measure on a finite-dimensional real inner product space is a positive multiple
of `volume` (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`), so the results proved for
`volume` pass to every additive Haar measure.

## Main declarations

* `EllipticPdes.H1Graph.smulMeasureL`: the continuous linear map `H1Graph (c • μ) Ω → H1Graph μ Ω`
  and its inverse `smulMeasureInvL`.
* `EllipticPdes.H1Graph.smulMeasureEquiv`: the resulting continuous linear equivalence.
* `EllipticPdes.H1Graph.smulMeasureL_mem_H01`: it maps `H₀¹` into `H₀¹`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.H1Graph

set_option linter.unusedSectionVars false

section LpRescale

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ρ ρ' : Measure α} {c : ℝ≥0}

/-- The identity on representatives, `L²(ρ') → L²(ρ)` for `ρ' = c • ρ`. -/
def lpSmulL (hc : c ≠ 0) (h : ρ' = c • ρ) : Lp F 2 ρ' →L[ℝ] Lp F 2 ρ :=
  Lp.LpToLpOfMeasureLeSMul (c := (c : ℝ≥0∞)⁻¹) (by simpa using hc) (by
    rw [h, ENNReal.smul_def, smul_smul, ENNReal.inv_mul_cancel (by simpa using hc)
      ENNReal.coe_ne_top, one_smul])

/-- The identity on representatives, `L²(ρ) → L²(ρ')` for `ρ' = c • ρ`. -/
def lpSmulInvL (h : ρ' = c • ρ) : Lp F 2 ρ →L[ℝ] Lp F 2 ρ' :=
  Lp.LpToLpOfMeasureLeSMul (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top (by rw [h, ENNReal.smul_def])

/-- `lpSmulL` is the identity on representatives. -/
lemma coeFn_lpSmulL (hc : c ≠ 0) (h : ρ' = c • ρ) (f : Lp F 2 ρ') :
    ⇑(lpSmulL hc h f) =ᵐ[ρ] ⇑f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- `lpSmulInvL` is the identity on representatives. -/
lemma coeFn_lpSmulInvL (h : ρ' = c • ρ) (f : Lp F 2 ρ) : ⇑(lpSmulInvL h f) =ᵐ[ρ'] ⇑f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- The smaller measure is absolutely continuous with respect to the larger multiple. -/
lemma absolutelyContinuous_of_smul (hc : c ≠ 0) (h : ρ' = c • ρ) : ρ ≪ ρ' :=
  Measure.absolutelyContinuous_of_le_smul (c := (c : ℝ≥0∞)⁻¹) (by
    rw [h, ENNReal.smul_def, smul_smul, ENNReal.inv_mul_cancel (by simpa using hc)
      ENNReal.coe_ne_top, one_smul])

/-- `lpSmulInvL` is a left inverse of `lpSmulL`. -/
lemma lpSmulInvL_lpSmulL (hc : c ≠ 0) (h : ρ' = c • ρ) (f : Lp F 2 ρ') :
    lpSmulInvL h (lpSmulL hc h f) = f := by
  refine Lp.ext ?_
  have hac : ρ' ≪ ρ := Measure.absolutelyContinuous_of_le_smul (c := (c : ℝ≥0∞))
    (by rw [h, ENNReal.smul_def])
  filter_upwards [coeFn_lpSmulInvL h (lpSmulL hc h f), hac.ae_eq (coeFn_lpSmulL hc h f)]
    with x h1 h2
  rw [h1, h2]

/-- `lpSmulL` is a left inverse of `lpSmulInvL`. -/
lemma lpSmulL_lpSmulInvL (hc : c ≠ 0) (h : ρ' = c • ρ) (f : Lp F 2 ρ) :
    lpSmulL hc h (lpSmulInvL h f) = f := by
  refine Lp.ext ?_
  have hac : ρ ≪ ρ' := absolutelyContinuous_of_smul hc h
  filter_upwards [coeFn_lpSmulL hc h (lpSmulInvL h f), hac.ae_eq (coeFn_lpSmulInvL h f)]
    with x h1 h2
  rw [h1, h2]

end LpRescale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ μ' : Measure E} {Ω : Set E}

/-- A continuous linear map of graph spaces from continuous linear maps on the function and
gradient parts. -/
def graphMap (A : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ'.restrict Ω))
    (B : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 (μ'.restrict Ω)) :
    H1Graph μ Ω →L[ℝ] H1Graph μ' Ω :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 (μ'.restrict Ω))
    (Lp E 2 (μ'.restrict Ω))).symm.toContinuousLinearMap.comp ((A.comp fnL).prod (B.comp gradL))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The function part of `graphMap A B U` is `A (fnL U)`. -/
@[simp] lemma fnL_graphMap (A : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ'.restrict Ω))
    (B : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 (μ'.restrict Ω)) (U : H1Graph μ Ω) :
    fnL (graphMap A B U) = A (fnL U) := rfl

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The gradient part of `graphMap A B U` is `B (gradL U)`. -/
@[simp] lemma gradL_graphMap (A : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ'.restrict Ω))
    (B : Lp E 2 (μ.restrict Ω) →L[ℝ] Lp E 2 (μ'.restrict Ω)) (U : H1Graph μ Ω) :
    gradL (graphMap A B U) = B (gradL U) := rfl

section Smul

variable (c : ℝ≥0) (hc : c ≠ 0) (μ Ω)

/-- The identity on representatives, `H1Graph (c • μ) Ω → H1Graph μ Ω`. -/
def smulMeasureL : H1Graph (c • μ) Ω →L[ℝ] H1Graph μ Ω :=
  graphMap (lpSmulL hc (Measure.restrict_smul c μ Ω)) (lpSmulL hc (Measure.restrict_smul c μ Ω))

/-- The identity on representatives, `H1Graph μ Ω → H1Graph (c • μ) Ω`. -/
def smulMeasureInvL : H1Graph μ Ω →L[ℝ] H1Graph (c • μ) Ω :=
  graphMap (lpSmulInvL (Measure.restrict_smul c μ Ω)) (lpSmulInvL (Measure.restrict_smul c μ Ω))

/-- **Rescaling the measure.** The identity on representatives is a continuous linear equivalence
`H1Graph (c • μ) Ω ≃L[ℝ] H1Graph μ Ω`. -/
def smulMeasureEquiv : H1Graph (c • μ) Ω ≃L[ℝ] H1Graph μ Ω :=
  ContinuousLinearEquiv.equivOfInverse (smulMeasureL μ Ω c hc) (smulMeasureInvL μ Ω c)
    (fun _ => ext (lpSmulInvL_lpSmulL hc _ _) (lpSmulInvL_lpSmulL hc _ _))
    (fun _ => ext (lpSmulL_lpSmulInvL hc _ _) (lpSmulL_lpSmulInvL hc _ _))

variable {μ Ω} [IsFiniteMeasureOnCompacts μ]

/-- The rescaling sends the graph of a test function to the graph of the same test function. -/
lemma smulMeasureL_testGraphₗ (hc : c ≠ 0) (φ : testFunctions Ω) :
    smulMeasureL μ Ω c hc (testGraphₗ (c • μ) Ω φ) = testGraphₗ μ Ω φ := by
  have hac : μ.restrict Ω ≪ (c • μ).restrict Ω :=
    absolutelyContinuous_of_smul hc (Measure.restrict_smul c μ Ω)
  refine ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [coeFn_lpSmulL hc (Measure.restrict_smul c μ Ω) (fnL (testGraphₗ (c • μ) Ω φ)),
      hac.ae_eq (coeFn_fnCls (μ := c • μ) φ), coeFn_fnCls (μ := μ) φ] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  · filter_upwards [coeFn_lpSmulL hc (Measure.restrict_smul c μ Ω) (gradL (testGraphₗ (c • μ) Ω φ)),
      hac.ae_eq (coeFn_gradCls (μ := c • μ) φ), coeFn_gradCls (μ := μ) φ] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)

/-- A continuous linear map of graph spaces that fixes test graphs maps `H₀¹` into `H₀¹`. -/
lemma mem_H01_of_map_testGraphₗ [IsFiniteMeasureOnCompacts μ']
    (T : H1Graph μ Ω →L[ℝ] H1Graph μ' Ω)
    (hT : ∀ φ : testFunctions Ω, T (testGraphₗ μ Ω φ) = testGraphₗ μ' Ω φ)
    {U : H1Graph μ Ω} (hU : U ∈ H01 μ Ω) : T U ∈ H01 μ' Ω := by
  have hcl : IsClosed (T ⁻¹' (H01 μ' Ω : Set (H1Graph μ' Ω))) :=
    (isClosed_H01 (μ := μ') (Ω := Ω)).preimage T.continuous
  refine H01_subset_of_isClosed hcl (fun φ => ?_) hU
  rw [Set.mem_preimage, hT φ]
  exact testGraphₗ_mem_H01 _

/-- The rescaling maps `H₀¹(c • μ, Ω)` into `H₀¹(μ, Ω)`. -/
lemma smulMeasureL_mem_H01 (hc : c ≠ 0) {U : H1Graph (c • μ) Ω} (hU : U ∈ H01 (c • μ) Ω) :
    smulMeasureL μ Ω c hc U ∈ H01 μ Ω :=
  mem_H01_of_map_testGraphₗ _ (smulMeasureL_testGraphₗ c hc) hU

/-- The rescaling restricted to `H₀¹`. -/
def smulMeasureH01 (hc : c ≠ 0) : H01 (c • μ) Ω →L[ℝ] H01 μ Ω :=
  ((smulMeasureL μ Ω c hc).comp (H01 (c • μ) Ω).subtypeL).codRestrict _ fun U =>
    smulMeasureL_mem_H01 c hc U.2

/-- **Compactness is invariant under rescaling the measure.** If `H₀¹(μ, Ω) ↪ L²(μ, Ω)` is
compact then so is `H₀¹(c • μ, Ω) ↪ L²(c • μ, Ω)`. -/
theorem embL2_isCompact_smul (hc : c ≠ 0) (hK : IsCompactOperator (embL2 μ Ω)) :
    IsCompactOperator (embL2 (c • μ) Ω) := by
  have h : embL2 (c • μ) Ω = (lpSmulInvL (Measure.restrict_smul c μ Ω) :
      Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 ((c • μ).restrict Ω)) ∘ (embL2 μ Ω) ∘
        smulMeasureH01 c hc := by
    funext U
    exact (lpSmulInvL_lpSmulL hc _ _).symm
  rw [h]
  exact (hK.comp_clm (smulMeasureH01 c hc)).clm_comp _

end Smul

end EllipticPdes.H1Graph
