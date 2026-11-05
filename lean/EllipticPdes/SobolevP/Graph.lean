/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Graph
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `W^{1,p}` graph space over a normed space

For a finite-dimensional real normed space `E`, a measure `μ` on `E`, a set `Ω ⊆ E` and an
exponent `p`, `W1pGraph p μ Ω` is `L^p(Ω) × L^p(Ω; E*)` with the `ℓ^p` product norm. A vector
`U` has a function part `fnL U` and a gradient part `gradL U`. The gradient takes values in the
dual `E* = StrongDual ℝ E`, so no inner product is needed. A test function `φ` embeds as the
graph `(φ, Dφ)`, and `W1p0 p μ Ω` is the closure of those graphs.

The inner-product space `E` of `Sobolev/Graph.lean` is the case `p = 2` with `E*` identified with
`E` by the Riesz map. The identification of `W1pGraph 2 μ Ω` with `H1Graph μ Ω` is a follow-up.

## Main declarations

* `EllipticPdes.W1pGraph`: the graph space `L^p(Ω) × L^p(Ω; E*)`.
* `EllipticPdes.W1pGraph.fnL`, `EllipticPdes.W1pGraph.gradL`: the continuous projections.
* `EllipticPdes.testFunctionsP`: test functions over a normed space.
* `EllipticPdes.W1pGraph.testGraphₗ`: the linear map `φ ↦ (φ, Dφ)` on test functions, with the
  pointwise form `EllipticPdes.W1pGraph.testGraph`.
* `EllipticPdes.W1p0`: the closure of the test graphs, with `EllipticPdes.isClosed_W1p0`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smooth compactly supported real functions with support in `Ω`, over a normed space. -/
def testFunctionsP (Ω : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨h1.add h1', h2.add h2', ?_⟩
    exact (closure_mono (Function.support_add φ ψ)).trans
      (by rw [closure_union]; exact Set.union_subset h3 h3')
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3⟩
    exact ⟨h1.const_smul c,
      h2.of_isClosed_subset isClosed_closure (tsupport_smul_subset_right (fun _ => c) φ),
      (tsupport_smul_subset_right (fun _ => c) φ).trans h3⟩

/-- `L^p(Ω) × L^p(Ω; E*)` with the `ℓ^p` product norm. The hypothesis `1 ≤ p` is unused in the
definition and makes the norm instances available at use sites. -/
@[nolint unusedArguments]
abbrev W1pGraph [MeasurableSpace E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E)
    (Ω : Set E) : Type _ :=
  WithLp p (Lp ℝ p (μ.restrict Ω) × Lp (StrongDual ℝ E) p (μ.restrict Ω))

namespace W1pGraph

variable [MeasurableSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} {Ω : Set E}

/-- The function part of a graph. -/
def fnL : W1pGraph p μ Ω →L[ℝ] Lp ℝ p (μ.restrict Ω) := WithLp.fstL p ℝ _ _

/-- The gradient part of a graph. -/
def gradL : W1pGraph p μ Ω →L[ℝ] Lp (StrongDual ℝ E) p (μ.restrict Ω) := WithLp.sndL p ℝ _ _

/-- The graph with function part `f` and gradient part `g`. -/
def mk (f : Lp ℝ p (μ.restrict Ω)) (g : Lp (StrongDual ℝ E) p (μ.restrict Ω)) :
    W1pGraph p μ Ω :=
  WithLp.toLp p (f, g)

@[simp] lemma fnL_mk (f : Lp ℝ p (μ.restrict Ω)) (g : Lp (StrongDual ℝ E) p (μ.restrict Ω)) :
    fnL (mk f g) = f := rfl

@[simp] lemma gradL_mk (f : Lp ℝ p (μ.restrict Ω)) (g : Lp (StrongDual ℝ E) p (μ.restrict Ω)) :
    gradL (mk f g) = g := rfl

end W1pGraph

section Derivative

variable {Ω : Set E} {φ : E → ℝ}

/-- The derivative is additive on test functions. -/
lemma fderiv_add_of_mem_testFunctionsP {ψ : E → ℝ} (h : φ ∈ testFunctionsP Ω)
    (h' : ψ ∈ testFunctionsP Ω) : fderiv ℝ (φ + ψ) = fderiv ℝ φ + fderiv ℝ ψ := by
  funext x
  exact fderiv_add (h.1.differentiable (by simp) x) (h'.1.differentiable (by simp) x)

/-- The derivative commutes with scalars on test functions. -/
lemma fderiv_const_smul_of_mem_testFunctionsP (h : φ ∈ testFunctionsP Ω) (c : ℝ) :
    fderiv ℝ (c • φ) = c • fderiv ℝ φ := by
  funext x
  exact fderiv_const_smul (h.1.differentiable (by simp) x) c

end Derivative

section TestGraph

variable [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ] {Ω : Set E} {φ : E → ℝ}

/-- A test function lies in `L^p(Ω)`. -/
lemma memLp_of_mem_testFunctionsP (h : φ ∈ testFunctionsP Ω) :
    MemLp φ p (μ.restrict Ω) :=
  h.1.continuous.memLp_of_hasCompactSupport h.2.1

/-- The derivative of a test function lies in `L^p(Ω; E*)`. -/
lemma memLp_fderiv_of_mem_testFunctionsP (h : φ ∈ testFunctionsP Ω) :
    MemLp (fderiv ℝ φ) p (μ.restrict Ω) :=
  (h.1.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (h.2.1.fderiv (𝕜 := ℝ))

namespace W1pGraph

variable [Fact (1 ≤ p)] (p μ Ω)

/-- The linear map `φ ↦ (φ, Dφ)` from test functions to the graph space. -/
def testGraphₗ : testFunctionsP Ω →ₗ[ℝ] W1pGraph p μ Ω where
  toFun φ := mk ((memLp_of_mem_testFunctionsP φ.2).toLp (φ : E → ℝ))
    ((memLp_fderiv_of_mem_testFunctionsP φ.2).toLp (fderiv ℝ (φ : E → ℝ)))
  map_add' φ ψ := by
    rw [WithLp.ext_iff]
    simp only [mk, WithLp.ofLp_add, Prod.mk_add_mk]
    congr 1
    · rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (fderiv_add_of_mem_testFunctionsP
        φ.2 ψ.2))
  map_smul' c φ := by
    rw [WithLp.ext_iff]
    simp only [mk, WithLp.ofLp_smul, Prod.smul_mk, RingHom.id_apply]
    congr 1
    · rw [← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq
        (fderiv_const_smul_of_mem_testFunctionsP φ.2 c))

variable {p μ Ω}

/-- The test graph `(φ, Dφ)` of a test function. -/
abbrev testGraph (φ : testFunctionsP Ω) : W1pGraph p μ Ω := testGraphₗ p μ Ω φ

/-- The function part of a test graph is the class of the test function. -/
lemma coeFn_fnL_testGraphₗ (φ : testFunctionsP Ω) :
    ⇑(fnL (testGraphₗ p μ Ω φ)) =ᵐ[μ.restrict Ω] φ :=
  (memLp_of_mem_testFunctionsP φ.2).coeFn_toLp

/-- The gradient part of a test graph is the classical derivative. -/
lemma coeFn_gradL_testGraphₗ (φ : testFunctionsP Ω) :
    ⇑(gradL (testGraphₗ p μ Ω φ)) =ᵐ[μ.restrict Ω] fderiv ℝ (φ : E → ℝ) :=
  (memLp_fderiv_of_mem_testFunctionsP φ.2).coeFn_toLp

end W1pGraph

end TestGraph

section W1p0

variable [MeasurableSpace E] [BorelSpace E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E)
  [IsFiniteMeasureOnCompacts μ] (Ω : Set E)

/-- `W₀^{1,p}(Ω)` as the closure of the test graphs. -/
def W1p0 : Submodule ℝ (W1pGraph p μ Ω) :=
  (LinearMap.range (W1pGraph.testGraphₗ p μ Ω)).topologicalClosure

/-- `W₀^{1,p}(Ω)` is closed in the graph space. -/
theorem isClosed_W1p0 : IsClosed (W1p0 p μ Ω : Set (W1pGraph p μ Ω)) :=
  Submodule.isClosed_topologicalClosure _

end W1p0

/-- Both graph spaces build for `p = 2` over an inner-product space. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    (μ : Measure F) (Ω : Set F) : Type _ × Type _ :=
  (W1pGraph 2 μ Ω, H1Graph μ Ω)

end EllipticPdes
