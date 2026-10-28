/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Wkp

/-!
# Spaces `H^k(U)` and `W_0^{k,p}(U)`

`H^k(U)` is `W^{k,2}(U)`. Its inner product is the restriction of the inner product of the
ambient product `L²(U)^N`. That inner product is the sum over multi-indices of the `L²` inner
products of the coordinates.

`W_0^{k,p}(U)` is the closure in `WkpGraph` of the graphs of the test functions of `U`. Entry
`α` of the graph of `φ` is the `L^p` class of the classical derivative `D^α φ`. A test function
is smooth with compact support. Each entry lies in `L^p(U)` for every `p ∈ [1, ∞]`.
`W^{k,p}(U)` is closed and contains each graph. The closure of their span therefore lies in it
and is complete.

## Main declarations

* `EllipticPdes.Sobolev.Hk`: the space `H^k(U) = W^{k,2}(U)`.
* `EllipticPdes.Sobolev.inner_Hk_eq`: the inner product of `H^k(U)` is the sum over
  `|α| ≤ k` of the `L²` inner products of the coordinates. Evans §5.2.2 Remark (i) (p. 258)
  states only that `H^k(U)` is a Hilbert space.
* `EllipticPdes.Sobolev.testGraph`: the graph of a test function in `WkpGraph`, linear in the
  function (`testGraph_add`, `testGraph_smul`, `testGraph_zero`).
* `EllipticPdes.Sobolev.W0kp`: the space `W_0^{k,p}(U)`.
* `EllipticPdes.Sobolev.testGraph_mem_W0kp`: the graph of a test function lies in it.
* `EllipticPdes.Sobolev.W0kp_le_Wkp`: `W_0^{k,p}(U) ≤ W^{k,p}(U)` (Evans §5.2.2 Definition,
  p. 259).

## References

* [evans-2010] L. C. Evans: *Partial Differential Equations* (2nd ed.) §5.2.2.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Set (EuclideanSpace ℝ (Fin d))}
  {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### `H^k(U)` -/

variable (d k U) in
/-- **Space `H^k(U) = W^{k,2}(U)`.** Evans §5.2.2 Remark (i) (p. 258). -/
abbrev Hk : Type := Wkp d k 2 U

/-- **Inner product of `H^k(U)`.** It is the sum over `|α| ≤ k` of the `L²(U)` inner products
of the coordinates. Evans §5.2.2 Remark (i) (p. 258) states that `H^k(U)` is a Hilbert space. -/
theorem inner_Hk_eq (u v : Hk d k U) :
    ⟪u, v⟫_ℝ = ∑ α, ⟪(u : WkpGraph d k 2 U) α, (v : WkpGraph d k 2 U) α⟫_ℝ := by
  change ⟪(u : WkpGraph d k 2 U), (v : WkpGraph d k 2 U)⟫_ℝ = _
  rw [PiLp.inner_apply]

/-! ### Graphs of test functions -/

omit [Fact (1 ≤ p)] in
/-- Each iterated derivative of a test function is smooth and compactly supported. It lies in
every `L^p(U)`. -/
theorem memLp_iterPartialD (h : IsTestFn U φ) (l : List (Fin d)) :
    MemLp (iterPartialD l φ) p (volume.restrict U) :=
  (h.iterPartialD l).continuous.memLp_of_hasCompactSupport (h.iterPartialD l).hasCompactSupport

/-- The iterated derivative is additive on smooth functions. -/
theorem iterPartialD_add (l : List (Fin d)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    iterPartialD l (φ + ψ) = iterPartialD l φ + iterPartialD l ψ := by
  induction l generalizing φ ψ with
  | nil => rfl
  | cons m l ih =>
    rw [iterPartialD_cons, iterPartialD_cons, iterPartialD_cons,
      partialD_add (hφ.differentiable (by simp)) (hψ.differentiable (by simp)) m]
    exact ih (contDiff_iterPartialD hφ [m]) (contDiff_iterPartialD hψ [m])

/-- The iterated derivative commutes with scalar multiplication on smooth functions. -/
theorem iterPartialD_smul (l : List (Fin d)) (c : ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    iterPartialD l (c • φ) = c • iterPartialD l φ := by
  induction l generalizing φ with
  | nil => rfl
  | cons m l ih =>
    rw [iterPartialD_cons, iterPartialD_cons,
      partialD_const_smul (hφ.differentiable (by simp)) c m]
    exact ih (contDiff_iterPartialD hφ [m])

/-- The iterated derivative of zero is zero. -/
theorem iterPartialD_zero (l : List (Fin d)) :
    iterPartialD l (0 : EuclideanSpace ℝ (Fin d) → ℝ) = 0 := by
  induction l with
  | nil => rfl
  | cons m l ih => rw [iterPartialD_cons, partialD_zero, ih]

/-- **Graph of a test function.** Entry `α` is the `L^p(U)` class of the classical derivative
`D^α φ`. -/
def testGraph (h : IsTestFn U φ) : WkpGraph d k p U :=
  WithLp.toLp p fun α : MultiIdx d k =>
    (memLp_iterPartialD h (MultiIdx.dirs α.toFun).reverse).toLp
      (iterPartialD (MultiIdx.dirs α.toFun).reverse φ)

omit [Fact (1 ≤ p)] in
/-- Entry `α` of `testGraph h` is the class of `D^α φ`. -/
theorem testGraph_apply (h : IsTestFn U φ) (α : MultiIdx d k) :
    (testGraph h : WkpGraph d k p U) α =
      (memLp_iterPartialD h (MultiIdx.dirs α.toFun).reverse).toLp
        (iterPartialD (MultiIdx.dirs α.toFun).reverse φ) := rfl

/-- The graph map is additive. -/
theorem testGraph_add (h : IsTestFn U φ) (h' : IsTestFn U ψ) :
    (testGraph h : WkpGraph d k p U) + testGraph h' = testGraph (h.add h') := by
  ext1 α
  rw [PiLp.add_apply, testGraph_apply, testGraph_apply, testGraph_apply, ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
  rw [iterPartialD_add _ h.contDiff h'.contDiff]

/-- The graph map commutes with scalar multiplication. -/
theorem testGraph_smul (c : ℝ) (h : IsTestFn U φ) :
    c • (testGraph h : WkpGraph d k p U) = testGraph (h.const_smul c) := by
  ext1 α
  rw [PiLp.smul_apply, testGraph_apply, testGraph_apply, ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => ?_)
  rw [iterPartialD_smul _ c h.contDiff]

/-- The graph of the zero test function is zero. -/
theorem testGraph_zero :
    (testGraph (IsTestFn.zero (Ω := U)) : WkpGraph d k p U) = 0 := by
  ext1 α
  rw [testGraph_apply, PiLp.zero_apply]
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_iterPartialD (p := p)
    (IsTestFn.zero (Ω := U)) (MultiIdx.dirs α.toFun).reverse),
    Lp.coeFn_zero ℝ p (volume.restrict U)] with x hx h0
  rw [hx, h0]
  simp [iterPartialD_zero]

variable (d k p U) in
/-- The set of graphs of test functions of `U`. -/
def wkpTestGraphs : Set (WkpGraph d k p U) :=
  {F | ∃ (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn U φ), F = testGraph h}

variable (d k p U) in
/-- **Space `W_0^{k,p}(U)`.** The closure in `WkpGraph` of the span of the graphs of the
test functions of `U`. Evans §5.2.2 Definition (p. 259). -/
def W0kp : Submodule ℝ (WkpGraph d k p U) :=
  (Submodule.span ℝ (wkpTestGraphs d k p U)).topologicalClosure

/-- The graph of a test function lies in `W_0^{k,p}(U)`. -/
theorem testGraph_mem_W0kp (h : IsTestFn U φ) : (testGraph h : WkpGraph d k p U) ∈ W0kp d k p U :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨φ, h, rfl⟩)

/-- The graph of a test function lies in `W^{k,p}(U)`: entry `α` is the weak `α`-th derivative
of entry `0`, since a smooth function has its classical derivative as weak derivative. -/
theorem testGraph_mem_Wkp (h : IsTestFn U φ) : (testGraph h : WkpGraph d k p U) ∈ Wkp d k p U := by
  rw [mem_Wkp_iff]
  intro α
  have h0 : MultiIdx.dirs (MultiIdx.zero (d := d) (k := k)).toFun = [] := by
    simp [MultiIdx.dirs, MultiIdx.zero, MultiIdx.toFun]
  have e0 : (testGraph h : WkpGraph d k p U) MultiIdx.zero =ᵐ[volume.restrict U] φ := by
    rw [testGraph_apply]
    filter_upwards [MemLp.coeFn_toLp (memLp_iterPartialD (p := p) h
      (MultiIdx.dirs (MultiIdx.zero (d := d) (k := k)).toFun).reverse)] with x hx
    rw [hx, h0]
    rfl
  have eα : (testGraph h : WkpGraph d k p U) α =ᵐ[volume.restrict U]
      iterPartialD (MultiIdx.dirs α.toFun).reverse φ := by
    rw [testGraph_apply]
    exact MemLp.coeFn_toLp _
  refine ⟨locallyIntegrableOn_lp _, locallyIntegrableOn_lp _, fun ψ hψ => ?_⟩
  have hw := (hasWeakDeriv_of_contDiff (U := U) h.contDiff α.toFun).2.2 ψ hψ
  have i0 : ∫ x in U, (testGraph h : WkpGraph d k p U) MultiIdx.zero x *
      iterPartialD (MultiIdx.dirs α.toFun) ψ x =
      ∫ x in U, φ x * iterPartialD (MultiIdx.dirs α.toFun) ψ x :=
    integral_congr_ae (e0.mul (Filter.EventuallyEq.refl _ _))
  have iα : ∫ x in U, (testGraph h : WkpGraph d k p U) α x * ψ x =
      ∫ x in U, iterPartialD (MultiIdx.dirs α.toFun).reverse φ x * ψ x :=
    integral_congr_ae (eα.mul (Filter.EventuallyEq.refl _ _))
  rw [i0, iα]
  exact hw

/-- **`W_0^{k,p}(U) ≤ W^{k,p}(U)`.** The graphs of the test functions lie in the closed
submodule `W^{k,p}(U)`, hence so does the closure of their span. Evans §5.2.2 Definition
(p. 259). -/
theorem W0kp_le_Wkp : W0kp d k p U ≤ Wkp d k p U := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) isClosed_Wkp
  rintro _ ⟨φ, h, rfl⟩
  exact testGraph_mem_Wkp h

/-- `W_0^{k,p}(U)` is complete: it is a topological closure in a complete space. -/
instance : CompleteSpace (W0kp d k p U) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℝ (wkpTestGraphs d k p U)).topologicalClosure)

end EllipticPdes.Sobolev
