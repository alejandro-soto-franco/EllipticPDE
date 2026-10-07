/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.WeakDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The graph space over a finite-dimensional inner product space

For a finite-dimensional real inner product space `E`, a measure `μ` on `E` and a set `Ω ⊆ E`,
`H1Graph μ Ω` is `L²(Ω) × L²(Ω; E)` with the `H¹` inner product `⟪u, v⟫ + ⟪∇u, ∇v⟫`. A vector
`U` has a function part `fnL U` and a gradient part `gradL U`. Test functions embed as the graphs
`φ ↦ (φ, ∇φ)`; `H01 μ Ω` is the closure of those graphs and `W12 μ Ω` is the orthogonal
complement of the constraint vectors `(∂_v φ, φ v)`, so that membership of `W12` is the weak
derivative identity. Both are closed subspaces of a Hilbert space, hence complete.

## Main declarations

* `EllipticPdes.H1Graph`: the graph space, with `fnL`, `gradL`, `mk`, `partialL`.
* `EllipticPdes.testFunctions`: smooth functions with compact support in `Ω`.
* `EllipticPdes.H1Graph.testGraphₗ`: the linear map `φ ↦ (φ, ∇φ)`.
* `EllipticPdes.H1Graph.W12`, `EllipticPdes.H1Graph.H01`: the Sobolev spaces.
* `EllipticPdes.H1Graph.mem_W12_iff_hasWeakFDerivOn`: `W12` is the space of functions with a
  weak derivative in `L²`.
* `EllipticPdes.H1Graph.H01_le_W12`: `H01 ≤ W12`, by integration by parts.
* `EllipticPdes.H1Graph.exists_seq_testGraphₗ_tendsto`: a member of `H01` is a limit of test
  graphs.
-/

@[expose] public section

open MeasureTheory TopologicalSpace Filter Topology
open scoped RealInnerProductSpace ENNReal Distributions

noncomputable section

namespace EllipticPdes

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Basic

variable [MeasurableSpace E]

/-- `L²(Ω) × L²(Ω; E)` with the `H¹` inner product. -/
abbrev H1Graph (μ : Measure E) (Ω : Set E) : Type _ :=
  WithLp 2 (Lp ℝ 2 (μ.restrict Ω) × Lp E 2 (μ.restrict Ω))

namespace H1Graph

variable {μ : Measure E} {Ω : Set E}

/-- The function component. -/
def fnL : H1Graph μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) := WithLp.fstL 2 ℝ _ _

/-- The gradient component, an `E`-valued `L²` field. -/
def gradL : H1Graph μ Ω →L[ℝ] Lp E 2 (μ.restrict Ω) := WithLp.sndL 2 ℝ _ _

/-- Build a graph vector from a function class and a gradient class. -/
def mk (f : Lp ℝ 2 (μ.restrict Ω)) (g : Lp E 2 (μ.restrict Ω)) : H1Graph μ Ω :=
  WithLp.toLp 2 (f, g)

/-- The function part of `mk f g` is `f`. -/
@[simp] lemma fnL_mk (f : Lp ℝ 2 (μ.restrict Ω)) (g : Lp E 2 (μ.restrict Ω)) :
    fnL (mk f g) = f := rfl

/-- The gradient part of `mk f g` is `g`. -/
@[simp] lemma gradL_mk (f : Lp ℝ 2 (μ.restrict Ω)) (g : Lp E 2 (μ.restrict Ω)) :
    gradL (mk f g) = g := rfl

/-- A graph vector is determined by its two components. -/
@[ext (iff := false)] lemma ext {U V : H1Graph μ Ω} (hf : fnL U = fnL V)
    (hg : gradL U = gradL V) : U = V :=
  WithLp.ofLp_injective 2 (Prod.ext hf hg)

/-- A graph vector is built from its two parts. -/
@[simp] lemma mk_fnL_gradL (U : H1Graph μ Ω) : mk (fnL U) (gradL U) = U := rfl

/-- The function part is additive. -/
@[simp] lemma fnL_add (U V : H1Graph μ Ω) : fnL (U + V) = fnL U + fnL V := rfl

/-- The gradient part is additive. -/
@[simp] lemma gradL_add (U V : H1Graph μ Ω) : gradL (U + V) = gradL U + gradL V := rfl

/-- The function part commutes with scalars. -/
@[simp] lemma fnL_smul (c : ℝ) (U : H1Graph μ Ω) : fnL (c • U) = c • fnL U := rfl

/-- The gradient part commutes with scalars. -/
@[simp] lemma gradL_smul (c : ℝ) (U : H1Graph μ Ω) : gradL (c • U) = c • gradL U := rfl

/-- The function part of zero is zero. -/
@[simp] lemma fnL_zero : fnL (0 : H1Graph μ Ω) = 0 := rfl

/-- The gradient part of zero is zero. -/
@[simp] lemma gradL_zero : gradL (0 : H1Graph μ Ω) = 0 := rfl

/-- The squared `H¹` norm is the sum of the squared `L²` norms of the two components. -/
lemma norm_sq_eq (U : H1Graph μ Ω) : ‖U‖ ^ 2 = ‖fnL U‖ ^ 2 + ‖gradL U‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 U

/-- The `H¹` inner product is the sum of the `L²` inner products of the components. -/
lemma inner_eq (U V : H1Graph μ Ω) : ⟪U, V⟫ = ⟪fnL U, fnL V⟫ + ⟪gradL U, gradL V⟫ :=
  WithLp.prod_inner_apply U V

/-- The function part is bounded by the `H¹` norm. -/
lemma norm_fnL_le (U : H1Graph μ Ω) : ‖fnL U‖ ≤ ‖U‖ := by
  have := norm_sq_eq U
  nlinarith [norm_nonneg (fnL U), norm_nonneg U, sq_nonneg ‖gradL U‖]

/-- The gradient part is bounded by the `H¹` norm. -/
lemma norm_gradL_le (U : H1Graph μ Ω) : ‖gradL U‖ ≤ ‖U‖ := by
  have := norm_sq_eq U
  nlinarith [norm_nonneg (gradL U), norm_nonneg U, sq_nonneg ‖fnL U‖]

/-- The directional weak derivative `∂_v u = ⟪v, ∇u⟫`. -/
def partialL (v : E) : H1Graph μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) :=
  ((innerSL ℝ v).compLpL 2 (μ.restrict Ω)).comp gradL

/-- A representative of the directional derivative is `x ↦ ⟪v, ∇u x⟫` almost everywhere. -/
lemma coeFn_partialL (v : E) (U : H1Graph μ Ω) :
    ⇑(partialL v U) =ᵐ[μ.restrict Ω] fun x => ⟪v, gradL U x⟫ :=
  (innerSL ℝ v).coeFn_compLpL (gradL U)

/-- The directional derivative is bounded by `‖v‖` times the `H¹` norm. -/
lemma norm_partialL_le (v : E) (U : H1Graph μ Ω) : ‖partialL v U‖ ≤ ‖v‖ * ‖U‖ := by
  have h : ‖(innerSL ℝ v).compLpL 2 (μ.restrict Ω) (gradL U)‖ ≤ ‖v‖ * ‖gradL U‖ :=
    ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ((innerSL ℝ v).norm_compLpL_le) (norm_nonneg _))).trans
      (by rw [innerSL_apply_norm])
  exact h.trans (mul_le_mul_of_nonneg_left (norm_gradL_le U) (norm_nonneg v))

/-- Convergence in the graph space is convergence of both components. -/
lemma tendsto_iff {ι : Type*} {l : Filter ι} {U : ι → H1Graph μ Ω} {V : H1Graph μ Ω} :
    Tendsto U l (𝓝 V) ↔
      Tendsto (fun n => fnL (U n)) l (𝓝 (fnL V)) ∧
        Tendsto (fun n => gradL (U n)) l (𝓝 (gradL V)) := by
  refine ⟨fun h => ⟨(fnL.continuous.tendsto V).comp h, (gradL.continuous.tendsto V).comp h⟩,
    fun ⟨h1, h2⟩ => ?_⟩
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.tendsto
    (fnL V, gradL V)).comp (h1.prodMk_nhds h2)


/-- The `L²` inner product of two classes of functions is the integral of the pairing. -/
lemma inner_toLp_toLp {α F : Type*} [MeasurableSpace α] {ν : Measure α} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f g : α → F} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, ⟪f x, g x⟫ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a ha hb
  rw [ha, hb]

/-- The `L²` inner product of the class of a function with another class. -/
lemma inner_toLp_left {α F : Type*} [MeasurableSpace α] {ν : Measure α} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f : α → F} (hf : MemLp f 2 ν) (g : Lp F 2 ν) :
    ⟪hf.toLp f, g⟫ = ∫ x, ⟪f x, g x⟫ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

end H1Graph

end Basic

/-- Smooth compactly supported real functions with support in `Ω`. -/
def testFunctions (Ω : Set E) : Submodule ℝ (E → ℝ) where
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

section TestFunctions

variable {Ω : Set E} {φ : E → ℝ}

/-- On an open set, `testFunctions Ω` is the set of underlying functions of Mathlib's test
functions `𝓓(Ω, ℝ)`. -/
lemma mem_testFunctions_iff_testFunction (hΩ : IsOpen Ω) :
    φ ∈ testFunctions Ω ↔ ∃ ψ : 𝓓((⟨Ω, hΩ⟩ : Opens E), ℝ), ⇑ψ = φ :=
  ⟨fun h => ⟨⟨φ, h.1, h.2.1, h.2.2⟩, rfl⟩,
    fun ⟨ψ, hψ⟩ => hψ ▸ ⟨ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset⟩⟩

/-- A test function is smooth. -/
lemma contDiff_of_mem (h : φ ∈ testFunctions Ω) : ContDiff ℝ (⊤ : ℕ∞) φ := h.1

/-- A directional derivative of a test function is continuous. -/
lemma continuous_fderiv_apply_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    Continuous fun x => fderiv ℝ φ x v :=
  (h.1.continuous_fderiv (by simp)).clm_apply continuous_const

/-- A directional derivative of a test function has compact support. -/
lemma hasCompactSupport_fderiv_apply_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    HasCompactSupport fun x => fderiv ℝ φ x v :=
  h.2.1.fderiv_apply ℝ v

/-- The field `x ↦ φ x • v` is continuous. -/
lemma continuous_smul_const_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    Continuous fun x => φ x • v :=
  h.1.continuous.smul continuous_const

/-- The field `x ↦ φ x • v` has compact support. -/
lemma hasCompactSupport_smul_const_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    HasCompactSupport fun x => φ x • v :=
  h.2.1.smul_right

section Gradient

variable [FiniteDimensional ℝ E]

/-- The inner product against the gradient is the derivative. -/
lemma inner_gradient_right (f : E → ℝ) (x v : E) : ⟪v, gradient f x⟫ = fderiv ℝ f x v := by
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]

/-- The gradient of a test function is continuous. -/
lemma continuous_gradient_of_mem (h : φ ∈ testFunctions Ω) : Continuous (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp (h.1.continuous_fderiv (by simp))

/-- The gradient of a test function has compact support. -/
lemma hasCompactSupport_gradient_of_mem (h : φ ∈ testFunctions Ω) :
    HasCompactSupport (gradient φ) :=
  (h.2.1.fderiv (𝕜 := ℝ)).comp_left (g := (InnerProductSpace.toDual ℝ E).symm) (map_zero _)

/-- The gradient is additive on test functions. -/
lemma gradient_add_of_mem {ψ : E → ℝ} (h : φ ∈ testFunctions Ω) (h' : ψ ∈ testFunctions Ω) :
    gradient (φ + ψ) = gradient φ + gradient ψ := by
  funext x
  simp only [gradient, Pi.add_apply]
  rw [fderiv_add (h.1.differentiable (by simp) x) (h'.1.differentiable (by simp) x), map_add]

/-- The gradient commutes with scalars on test functions. -/
lemma gradient_smul_of_mem (h : φ ∈ testFunctions Ω) (c : ℝ) :
    gradient (c • φ) = c • gradient φ := by
  funext x
  simp only [gradient, Pi.smul_apply]
  rw [fderiv_const_smul (h.1.differentiable (by simp) x) c, map_smul]

end Gradient

section Integrable

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- A test function lies in `L²(Ω)`. -/
lemma memLp_of_mem (h : φ ∈ testFunctions Ω) : MemLp φ 2 (μ.restrict Ω) :=
  h.1.continuous.memLp_of_hasCompactSupport h.2.1

/-- A directional derivative of a test function lies in `L²(Ω)`. -/
lemma memLp_fderiv_apply_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    MemLp (fun x => fderiv ℝ φ x v) 2 (μ.restrict Ω) :=
  (continuous_fderiv_apply_of_mem h v).memLp_of_hasCompactSupport
    (hasCompactSupport_fderiv_apply_of_mem h v)

/-- The field `x ↦ φ x • v` lies in `L²(Ω; E)`. -/
lemma memLp_smul_const_of_mem (h : φ ∈ testFunctions Ω) (v : E) :
    MemLp (fun x => φ x • v) 2 (μ.restrict Ω) :=
  (continuous_smul_const_of_mem h v).memLp_of_hasCompactSupport
    (hasCompactSupport_smul_const_of_mem h v)

end Integrable

section GradientIntegrable

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [IsFiniteMeasureOnCompacts μ]

/-- The gradient of a test function lies in `L²(Ω; E)`. -/
lemma memLp_gradient_of_mem (h : φ ∈ testFunctions Ω) :
    MemLp (gradient φ) 2 (μ.restrict Ω) :=
  (continuous_gradient_of_mem h).memLp_of_hasCompactSupport (hasCompactSupport_gradient_of_mem h)

end GradientIntegrable

end TestFunctions

namespace H1Graph

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section FiniteOnCompacts

variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ] (Ω : Set E)

/-- The `L²(Ω)` class of a test function. -/
def fnCls (φ : testFunctions Ω) : Lp ℝ 2 (μ.restrict Ω) := (memLp_of_mem φ.2).toLp (φ : E → ℝ)

/-- The `L²(Ω; E)` class of the gradient of a test function. -/
def gradCls (φ : testFunctions Ω) : Lp E 2 (μ.restrict Ω) :=
  (memLp_gradient_of_mem φ.2).toLp (gradient (φ : E → ℝ))

/-- The `L²(Ω)` class of the derivative `∂_v φ` of a test function. -/
def partialCls (φ : testFunctions Ω) (v : E) : Lp ℝ 2 (μ.restrict Ω) :=
  (memLp_fderiv_apply_of_mem φ.2 v).toLp fun x => fderiv ℝ (φ : E → ℝ) x v

/-- The `L²(Ω; E)` class of the field `x ↦ φ x • v`. -/
def smulCls (φ : testFunctions Ω) (v : E) : Lp E 2 (μ.restrict Ω) :=
  (memLp_smul_const_of_mem φ.2 v).toLp fun x => (φ : E → ℝ) x • v

variable {μ Ω}

omit [FiniteDimensional ℝ E] in
/-- A representative of `fnCls` is the test function almost everywhere. -/
lemma coeFn_fnCls (φ : testFunctions Ω) : ⇑(fnCls μ Ω φ) =ᵐ[μ.restrict Ω] φ :=
  (memLp_of_mem φ.2).coeFn_toLp

/-- A representative of `gradCls` is the classical gradient almost everywhere. -/
lemma coeFn_gradCls (φ : testFunctions Ω) :
    ⇑(gradCls μ Ω φ) =ᵐ[μ.restrict Ω] gradient (φ : E → ℝ) :=
  (memLp_gradient_of_mem φ.2).coeFn_toLp

omit [FiniteDimensional ℝ E] in
/-- A representative of `partialCls` is the classical directional derivative. -/
lemma coeFn_partialCls (φ : testFunctions Ω) (v : E) :
    ⇑(partialCls μ Ω φ v) =ᵐ[μ.restrict Ω] fun x => fderiv ℝ (φ : E → ℝ) x v :=
  (memLp_fderiv_apply_of_mem φ.2 v).coeFn_toLp

omit [FiniteDimensional ℝ E] in
/-- A representative of `smulCls` is `x ↦ φ x • v` almost everywhere. -/
lemma coeFn_smulCls (φ : testFunctions Ω) (v : E) :
    ⇑(smulCls μ Ω φ v) =ᵐ[μ.restrict Ω] fun x => (φ : E → ℝ) x • v :=
  (memLp_smul_const_of_mem φ.2 v).coeFn_toLp

variable (μ Ω)

/-- The linear map `φ ↦ (φ, ∇φ)` from test functions to the graph space. -/
def testGraphₗ : testFunctions Ω →ₗ[ℝ] H1Graph μ Ω where
  toFun φ := WithLp.toLp 2 (fnCls μ Ω φ, gradCls μ Ω φ)
  map_add' φ ψ := by
    rw [WithLp.ext_iff]
    simp only [WithLp.ofLp_add, Prod.mk_add_mk, fnCls, gradCls]
    congr 1
    · rw [← MemLp.toLp_add]
      exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (gradient_add_of_mem φ.2 ψ.2))
  map_smul' c φ := by
    rw [WithLp.ext_iff]
    simp only [WithLp.ofLp_smul, Prod.smul_mk, RingHom.id_apply, fnCls, gradCls]
    congr 1
    · rw [← MemLp.toLp_const_smul]
      exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (gradient_smul_of_mem φ.2 c))

variable {μ Ω}

/-- The function part of a test graph is the class of the test function. -/
@[simp] lemma fnL_testGraphₗ (φ : testFunctions Ω) : fnL (testGraphₗ μ Ω φ) = fnCls μ Ω φ := rfl

/-- The gradient part of a test graph is the class of the classical gradient. -/
@[simp] lemma gradL_testGraphₗ (φ : testFunctions Ω) :
    gradL (testGraphₗ μ Ω φ) = gradCls μ Ω φ := rfl

/-- A representative of the function part of a test graph is the test function. -/
lemma coeFn_fnL_testGraphₗ (φ : testFunctions Ω) :
    ⇑(fnL (testGraphₗ μ Ω φ)) =ᵐ[μ.restrict Ω] φ :=
  coeFn_fnCls φ

/-- A representative of the gradient part of a test graph is the classical gradient. -/
lemma coeFn_gradL_testGraphₗ (φ : testFunctions Ω) :
    ⇑(gradL (testGraphₗ μ Ω φ)) =ᵐ[μ.restrict Ω] gradient (φ : E → ℝ) :=
  coeFn_gradCls φ

/-- The directional derivative of a test graph is the classical directional derivative. -/
lemma partialL_testGraphₗ (v : E) (φ : testFunctions Ω) :
    partialL v (testGraphₗ μ Ω φ) = partialCls μ Ω φ v := by
  refine Lp.ext ?_
  filter_upwards [coeFn_partialL v (testGraphₗ μ Ω φ), coeFn_gradCls φ,
    coeFn_partialCls φ v] with x h1 h2 h3
  rw [h1, h3, gradL_testGraphₗ, h2, inner_gradient_right]

variable (μ Ω)

/-- Constraint vector `(∂_v φ, φ v)`: orthogonality to it is one instance of the weak
derivative identity. -/
def constraintVec (φ : testFunctions Ω) (v : E) : H1Graph μ Ω :=
  mk (partialCls μ Ω φ v) (smulCls μ Ω φ v)

/-- `W^{1,2}(Ω)` as an orthogonal complement. -/
def W12 : Submodule ℝ (H1Graph μ Ω) :=
  (Submodule.span ℝ (Set.range fun p : testFunctions Ω × E => constraintVec μ Ω p.1 p.2))ᗮ

/-- `H₀¹(Ω)` as the closure of the test graphs. -/
def H01 : Submodule ℝ (H1Graph μ Ω) :=
  (LinearMap.range (testGraphₗ μ Ω)).topologicalClosure

/-- `W^{1,2}(Ω)` is complete, being an orthogonal complement in a Hilbert space. -/
instance : CompleteSpace (W12 μ Ω) := by unfold W12; infer_instance

/-- `H₀¹(Ω)` is complete, being a closed subspace of a Hilbert space. -/
instance : CompleteSpace (H01 μ Ω) := by unfold H01; infer_instance

/-- The inclusion `H₀¹(Ω) → L²(Ω)`. -/
def embL2 : H01 μ Ω →L[ℝ] Lp ℝ 2 (μ.restrict Ω) := fnL.comp (H01 μ Ω).subtypeL

variable {μ Ω}

/-- The inclusion `H₀¹(Ω) → L²(Ω)` takes the function part. -/
lemma embL2_apply (U : H01 μ Ω) : embL2 μ Ω U = fnL (U : H1Graph μ Ω) := rfl

/-- The inclusion `H₀¹(Ω) → L²(Ω)` has norm at most one. -/
lemma norm_embL2_le (U : H01 μ Ω) : ‖embL2 μ Ω U‖ ≤ ‖U‖ := norm_fnL_le (U : H1Graph μ Ω)

omit [FiniteDimensional ℝ E] in
/-- The pairing of a constraint vector against `U` extracts the weak derivative relation. -/
lemma inner_constraintVec (φ : testFunctions Ω) (v : E) (U : H1Graph μ Ω) :
    ⟪constraintVec μ Ω φ v, U⟫ = ⟪partialCls μ Ω φ v, fnL U⟫ + ⟪smulCls μ Ω φ v, gradL U⟫ :=
  inner_eq _ _

omit [FiniteDimensional ℝ E] in
/-- Membership of `W^{1,2}(Ω)` is orthogonality to every constraint vector. -/
lemma mem_W12_iff (U : H1Graph μ Ω) :
    U ∈ W12 μ Ω ↔ ∀ (φ : testFunctions Ω) (v : E), ⟪constraintVec μ Ω φ v, U⟫ = 0 := by
  rw [W12, Submodule.mem_orthogonal]
  refine ⟨fun hU φ v => hU _ (Submodule.subset_span ⟨(φ, v), rfl⟩), fun hU u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨φ, v⟩, rfl⟩ := hx; exact hU φ v
  | zero => simp
  | add x y _ _ ihx ihy => rw [inner_add_left, ihx, ihy, add_zero]
  | smul c x _ ih => rw [inner_smul_left]; simp [ih]

/-- A test graph lies in `H₀¹(Ω)`. -/
lemma testGraphₗ_mem_H01 (φ : testFunctions Ω) : testGraphₗ μ Ω φ ∈ H01 μ Ω :=
  Submodule.le_topologicalClosure _ ⟨φ, rfl⟩

/-- A closed subset containing every test graph contains `H₀¹(Ω)`. -/
theorem H01_subset_of_isClosed {S : Set (H1Graph μ Ω)} (hS : IsClosed S)
    (h : ∀ φ, testGraphₗ μ Ω φ ∈ S) : (H01 μ Ω : Set (H1Graph μ Ω)) ⊆ S :=
  closure_minimal (by rintro _ ⟨φ, rfl⟩; exact h φ) hS

/-- A closed submodule containing every test graph contains `H₀¹(Ω)`. -/
theorem H01_le_of_isClosed {S : Submodule ℝ (H1Graph μ Ω)} (hS : IsClosed (S : Set (H1Graph μ Ω)))
    (h : ∀ φ, testGraphₗ μ Ω φ ∈ S) : H01 μ Ω ≤ S :=
  H01_subset_of_isClosed hS h

/-- Every element of `H₀¹(Ω)` is the limit of the graphs of a sequence of test functions. -/
theorem exists_seq_testGraphₗ_tendsto {U : H1Graph μ Ω} (hU : U ∈ H01 μ Ω) :
    ∃ φ : ℕ → testFunctions Ω, Tendsto (fun n => testGraphₗ μ Ω (φ n)) atTop (𝓝 U) := by
  have hU' : U ∈ closure (LinearMap.range (testGraphₗ μ Ω) : Set (H1Graph μ Ω)) := by
    rwa [← Submodule.topologicalClosure_coe]
  obtain ⟨X, hX, hXt⟩ := mem_closure_iff_seq_limit.mp hU'
  choose φ hφ using fun n => (hX n : ∃ φ, testGraphₗ μ Ω φ = X n)
  exact ⟨φ, by simpa only [hφ] using hXt⟩

/-- The squared norm of a test graph is `∫ φ² + ∫ ‖∇φ‖²` over `Ω`. -/
lemma norm_sq_testGraphₗ (φ : testFunctions Ω) :
    ‖testGraphₗ μ Ω φ‖ ^ 2 =
      ∫ x in Ω, (φ : E → ℝ) x ^ 2 ∂μ + ∫ x in Ω, ‖gradient (φ : E → ℝ) x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq, fnL_testGraphₗ, gradL_testGraphₗ, ← real_inner_self_eq_norm_sq (fnCls μ Ω φ),
    ← real_inner_self_eq_norm_sq (gradCls μ Ω φ), fnCls, gradCls, inner_toLp_toLp,
    inner_toLp_toLp]
  simp [sq]

/-- The test graph map sends `φ` to the pair of its two classes. -/
lemma testGraphₗ_apply (φ : testFunctions Ω) :
    testGraphₗ μ Ω φ = mk (fnCls μ Ω φ) (gradCls μ Ω φ) := rfl

omit [FiniteDimensional ℝ E] in
/-- `W^{1,2}(Ω)` is closed in the graph space. -/
lemma isClosed_W12 : IsClosed (W12 μ Ω : Set (H1Graph μ Ω)) :=
  Submodule.isClosed_orthogonal _

/-- `H₀¹(Ω)` is closed in the graph space. -/
lemma isClosed_H01 : IsClosed (H01 μ Ω : Set (H1Graph μ Ω)) :=
  Submodule.isClosed_topologicalClosure _

end FiniteOnCompacts

section Haar

variable {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- Integration by parts for two test functions over the whole space. -/
lemma integral_fderiv_mul_eq_neg (φ ψ : testFunctions Ω) (v : E) :
    ∫ x, fderiv ℝ (ψ : E → ℝ) x v * (φ : E → ℝ) x ∂μ =
      -∫ x, (ψ : E → ℝ) x * fderiv ℝ (φ : E → ℝ) x v ∂μ := by
  have h := ((hasWeakFDerivOn_fderiv (Ω := ⊤) (μ := μ)
    (((contDiff_of_mem φ.2).of_le (by exact_mod_cast le_top)).contDiffOn)) v).integral_eq
    (contDiff_of_mem ψ.2) ψ.2.2.1 (by simp)
  simpa using h

/-- A test graph lies in `W^{1,2}(Ω)`: its function part has its classical gradient as weak
gradient. This is integration by parts, with no boundary term by compact support. -/
theorem testGraphₗ_mem_W12 (φ : testFunctions Ω) : testGraphₗ μ Ω φ ∈ W12 μ Ω := by
  rw [mem_W12_iff]
  intro ψ v
  rw [inner_constraintVec, fnL_testGraphₗ, gradL_testGraphₗ, partialCls, fnCls, smulCls, gradCls,
    inner_toLp_toLp, inner_toLp_toLp]
  have e1 : ∫ x in Ω, ⟪fderiv ℝ (ψ : E → ℝ) x v, (φ : E → ℝ) x⟫ ∂μ =
      ∫ x, fderiv ℝ (ψ : E → ℝ) x v * (φ : E → ℝ) x ∂μ :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (ψ.2.2.2 h))]; simp))
  have e2 : ∫ x in Ω, ⟪(ψ : E → ℝ) x • v, gradient (φ : E → ℝ) x⟫ ∂μ =
      ∫ x, (ψ : E → ℝ) x * fderiv ℝ (φ : E → ℝ) x v ∂μ :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp)).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ψ.2.2.2 h)), zero_mul]))
  rw [e1, e2, integral_fderiv_mul_eq_neg, neg_add_cancel]

/-- `H₀¹(Ω)` lies in `W^{1,2}(Ω)`: every element of `H₀¹` has a weak `L²` gradient. -/
theorem H01_le_W12 : H01 μ Ω ≤ W12 μ Ω :=
  H01_le_of_isClosed (Submodule.isClosed_orthogonal _) (testGraphₗ_mem_W12 (μ := μ))

end Haar

section WeakDerivative

variable {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {Ω : Set E}

omit [FiniteDimensional ℝ E] in
/-- The pairing against a constraint vector as integrals over the whole space, for any
representatives of the components of `U`. -/
lemma inner_constraintVec_eq_integral (φ : testFunctions Ω) (v : E) (U : H1Graph μ Ω) :
    ⟪constraintVec μ Ω φ v, U⟫ =
      ∫ x, fderiv ℝ (φ : E → ℝ) x v • fnL U x ∂μ +
        ∫ x, (φ : E → ℝ) x • innerSL ℝ (gradL U x) v ∂μ := by
  rw [inner_constraintVec, partialCls, smulCls, inner_toLp_left, inner_toLp_left]
  congr 1
  · refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_))
    · simp [mul_comm]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (φ.2.2.2 h))]; simp
  · refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_))
    · simp [real_inner_comm, real_inner_smul_left]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.2.2.2 h))]; simp

/-- An `L²(Ω)` class is locally integrable on `Ω`. -/
lemma locallyIntegrableOn_lp {F : Type*} [NormedAddCommGroup F]
    (f : Lp F 2 (μ.restrict Ω)) : LocallyIntegrableOn f Ω μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp f).locallyIntegrable (by norm_num))

/-- The component `x ↦ ⟪∇u x, v⟫` of a gradient is locally integrable on `Ω`. -/
lemma locallyIntegrableOn_innerSL_gradL (v : E) (U : H1Graph μ Ω) :
    LocallyIntegrableOn (fun x => innerSL ℝ (gradL U x) v) Ω μ :=
  locallyIntegrableOn_of_locallyIntegrable_restrict
    (((Lp.memLp (partialL v U)).locallyIntegrable (by norm_num)).congr
      ((coeFn_partialL v U).mono fun x hx => by simp [hx, real_inner_comm]))

/-- **`W^{1,2}(Ω)` is the space of functions with a weak gradient in `L²`.** -/
theorem mem_W12_iff_hasWeakFDerivOn (hΩ : IsOpen Ω) (U : H1Graph μ Ω) :
    U ∈ W12 μ Ω ↔
      HasWeakFDerivOn ⟨Ω, hΩ⟩ (fnL U) (fun x => innerSL ℝ (gradL U x)) μ := by
  rw [mem_W12_iff]
  refine ⟨fun h v => hasWeakLineDerivOn_iff.2 ⟨locallyIntegrableOn_lp _,
    locallyIntegrableOn_innerSL_gradL v U, fun ψ hψ hc hs => ?_⟩, fun h ψ v => ?_⟩
  · have := h ⟨ψ, hψ, hc, hs⟩ v
    rw [inner_constraintVec_eq_integral, add_eq_zero_iff_eq_neg] at this
    exact this
  · rw [inner_constraintVec_eq_integral, add_eq_zero_iff_eq_neg]
    exact (h v).integral_eq ψ.2.1 ψ.2.2.1 ψ.2.2.2

end WeakDerivative

end H1Graph

end EllipticPdes
