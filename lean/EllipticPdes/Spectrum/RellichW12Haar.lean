/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.RellichW12
public import EllipticPdes.Spectrum.RellichHaar
public import EllipticPdes.Sobolev.GraphEuclidean

/-!
# Rellich on `W^{1,2}(Ω)` for any additive Haar measure

`Sobolev.embW12_isCompact` states Rellich on `W^{1,2}(Ω)` in coordinates for a bounded open set
with `C¹` boundary. `H1Graph.w12Equiv` transfers it to the graph space `H1Graph.W12 volume Ω`.
Rescaling the measure by `c > 0` rescales the inner product of the graph space by `c`, so the
identity on representatives sends `W^{1,2}` for `c • volume` onto `W^{1,2}` for `volume`, and the
embedding stays compact.

## Main declarations

* `EllipticPdes.H1Graph.embW12G`: the function part on `H1Graph.W12 μ Ω`.
* `EllipticPdes.H1Graph.smulMeasureL_mem_W12_iff`: the rescaling preserves `W^{1,2}`.
* `EllipticPdes.H1Graph.embW12G_isCompact_haar`: Rellich on `W^{1,2}(Ω)` for any additive Haar
  measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.H1Graph

section Embedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (Ω : Set E)

/-- The function part on `W^{1,2}(Ω)`, as a continuous linear map into `L²(Ω)`. -/
def embW12G : W12 μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) := fnL.comp (W12 μ Ω).subtypeL

end Embedding

variable {d : ℕ}

/-- `embW12G` for the volume of `ℝᵈ` is the coordinate embedding read through `w12Equiv`. -/
theorem embW12G_eq_embW12 (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    ⇑(embW12G volume Ω) = ⇑(Sobolev.embW12 Ω) ∘ ⇑(w12Equiv Ω).symm := by
  funext U
  simp only [Function.comp_apply, Sobolev.embW12_apply]
  rw [← fnL_w12Equiv, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **Rellich on `W^{1,2}(Ω)` in the graph space for the volume.** -/
theorem embW12G_isCompact (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω) :
    IsCompactOperator (embW12G volume Ω) := by
  rw [embW12G_eq_embW12]
  exact (Sobolev.embW12_isCompact hd hΩo hΩb hC1).comp_clm
    (w12Equiv Ω).symm.toContinuousLinearEquiv.toContinuousLinearMap

section Smul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ν : Measure E} {Ω : Set E} {c : ℝ≥0}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Rescaling the measure rescales the inner product of the graph space.** -/
theorem inner_eq_smul_inner_smulMeasureL (hc : c ≠ 0) (U V : H1Graph (c • ν) Ω) :
    ⟪U, V⟫ = c * ⟪smulMeasureL ν Ω c hc U, smulMeasureL ν Ω c hc V⟫ := by
  rw [inner_eq, inner_eq, inner_eq_smul_inner_lpSmulL hc (Measure.restrict_smul c ν Ω) (fnL U),
    inner_eq_smul_inner_lpSmulL hc (Measure.restrict_smul c ν Ω) (gradL U), mul_add]
  rfl

variable [IsFiniteMeasureOnCompacts ν]

omit [FiniteDimensional ℝ E] in
/-- The rescaling sends a constraint vector to the constraint vector of the same test function. -/
theorem smulMeasureL_constraintVec (hc : c ≠ 0) (φ : testFunctions Ω) (v : E) :
    smulMeasureL ν Ω c hc (constraintVec (c • ν) Ω φ v) = constraintVec ν Ω φ v := by
  have hac : ν.restrict Ω ≪ (c • ν).restrict Ω :=
    absolutelyContinuous_of_smul hc (Measure.restrict_smul c ν Ω)
  refine ext (Lp.ext ?_) (Lp.ext ?_)
  · filter_upwards [coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω)
        (fnL (constraintVec (c • ν) Ω φ v)),
      hac.ae_eq (coeFn_partialCls (μ := c • ν) φ v), coeFn_partialCls (μ := ν) φ v] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  · filter_upwards [coeFn_lpSmulL hc (Measure.restrict_smul c ν Ω)
        (gradL (constraintVec (c • ν) Ω φ v)),
      hac.ae_eq (coeFn_smulCls (μ := c • ν) φ v), coeFn_smulCls (μ := ν) φ v] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)

omit [FiniteDimensional ℝ E] in
/-- **Rescaling preserves `W^{1,2}`.** -/
theorem smulMeasureL_mem_W12_iff (hc : c ≠ 0) (U : H1Graph (c • ν) Ω) :
    smulMeasureL ν Ω c hc U ∈ W12 ν Ω ↔ U ∈ W12 (c • ν) Ω := by
  rw [mem_W12_iff, mem_W12_iff]
  refine forall_congr' fun φ => forall_congr' fun v => ?_
  rw [inner_eq_smul_inner_smulMeasureL hc, smulMeasureL_constraintVec hc, mul_eq_zero,
    or_iff_right (NNReal.coe_ne_zero.2 hc)]

omit [FiniteDimensional ℝ E] in
/-- The rescaling maps `W^{1,2}(c • ν, Ω)` into `W^{1,2}(ν, Ω)`. -/
theorem smulMeasureL_mem_W12 (hc : c ≠ 0) {U : H1Graph (c • ν) Ω} (hU : U ∈ W12 (c • ν) Ω) :
    smulMeasureL ν Ω c hc U ∈ W12 ν Ω :=
  (smulMeasureL_mem_W12_iff hc U).2 hU

/-- The rescaling restricted to `W^{1,2}`. -/
def smulMeasureW12 (hc : c ≠ 0) : W12 (c • ν) Ω →L[ℝ] W12 ν Ω :=
  ((smulMeasureL ν Ω c hc).comp (W12 (c • ν) Ω).subtypeL).codRestrict _ fun U =>
    smulMeasureL_mem_W12 hc U.2

omit [FiniteDimensional ℝ E] in
/-- **Compactness on `W^{1,2}` is invariant under rescaling the measure.** -/
theorem embW12G_isCompact_smul (hc : c ≠ 0) (hK : IsCompactOperator (embW12G ν Ω)) :
    IsCompactOperator (embW12G (c • ν) Ω) := by
  convert (hK.comp_clm (smulMeasureW12 hc)).clm_comp
    (lpSmulInvL (Measure.restrict_smul c ν Ω) :
      Lp ℝ 2 (ν.restrict Ω) →L[ℝ] Lp ℝ 2 ((c • ν).restrict Ω)) using 1
  funext U
  exact (lpSmulInvL_lpSmulL hc _ _).symm

end Smul

/-- **Rellich on `W^{1,2}(Ω)` for any additive Haar measure.** For a bounded open set with `C¹`
boundary in `ℝᵈ`, `d > 0`, the embedding `W^{1,2}(Ω) ↪ L²(Ω)` is compact. -/
theorem embW12G_isCompact_haar (hd : 0 < d) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [μ.IsAddHaarMeasure] {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hC1 : Extension.HasC1Boundary Ω) :
    IsCompactOperator (embW12G μ Ω) := by
  obtain ⟨c, hc, rfl⟩ := exists_eq_smul_volume μ
  exact embW12G_isCompact_smul hc (embW12G_isCompact hd hΩo hΩb hC1)

end EllipticPdes.H1Graph
