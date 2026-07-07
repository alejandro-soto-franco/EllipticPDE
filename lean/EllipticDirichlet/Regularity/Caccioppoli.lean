/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Garding
import EllipticDirichlet.Regularity.DiffQuotientBound

/-!
# Caccioppoli (interior energy) estimate

The first-derivative interior estimate: for a weak solution of `L u = f`, the energy
`∫_V |∇u|²` is bounded by the data on a slightly larger set `W`. Obtained by testing
the weak formulation with `ζ² u`, using uniform ellipticity from below and Young's
inequality to absorb the gradient term. See Gilbarg-Trudinger, *Elliptic PDE of
Second Order*, Theorem 8.8, and Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1.

## The cutoff-multiplication keystone

The test function `ζ² u` for `u ∈ H₀¹(Ω)` is not directly available from the graph
encoding of `Sobolev/Basic.lean`. We build it here. For a smooth compactly supported
cutoff `η` (an [`IsTestFn`]) we assemble the **cutoff-multiplication operator** on the
ambient graph space,

  `(cutoffMul η U)₀ = η · U₀`,   `(cutoffMul η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`,

which is exactly the Leibniz rule `∇(η u) = η ∇u + (∇η) u`. It is a bounded operator, it
sends the graph of a test function `φ` to the graph of the product `η φ`, hence by
closure it maps `H₀¹(Ω)` into itself: [`cutoffMul_mem_H01`].
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ}

/-! ### Global sup bounds for a test function and its partials -/

/-- A smooth compactly supported function is globally bounded in absolute value. -/
lemma exists_abs_bound {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) : ∃ M : ℝ, ∀ x, |φ x| ≤ M := by
  obtain ⟨C, hC⟩ := h.continuous.bounded_above_of_compact_support h.2.1
  exact ⟨C, fun x => by have := hC x; rwa [Real.norm_eq_abs] at this⟩

/-- Each partial derivative of a test function is globally bounded in absolute value. -/
lemma exists_abs_bound_partialD {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ) (i : Fin d) :
    ∃ M : ℝ, ∀ x, |partialD i φ x| ≤ M := by
  obtain ⟨C, hC⟩ := (h.continuous_partialD i).bounded_above_of_compact_support
    (h.hasCompactSupport_partialD i)
  exact ⟨C, fun x => by have := hC x; rwa [Real.norm_eq_abs] at this⟩

/-! ### The multiplier actions of a cutoff on `L²(Ω)` -/

/-- Multiplication by the cutoff `η` on `L²(Ω)`, as a continuous linear map. -/
def mulTest {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL h.continuous.measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound h).choose_spec)

/-- Multiplication by the partial `∂ᵢη` of the cutoff on `L²(Ω)`, continuous linear map. -/
def mulTestPartial {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (h.continuous_partialD i).measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound_partialD h i).choose_spec)

/-- The a.e. representative of `mulTest`: `mulTest h g =ᵐ x ↦ η x · g x`. -/
lemma mulTest_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) (g : L2D Ω) :
    mulTest h g =ᵐ[volume.restrict Ω] fun x => η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- The a.e. representative of `mulTestPartial`: `mulTestPartial h i g =ᵐ x ↦ ∂ᵢη x · g x`. -/
lemma mulTestPartial_coeFn {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (i : Fin d) (g : L2D Ω) :
    mulTestPartial h i g =ᵐ[volume.restrict Ω] fun x => partialD i η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-! ### The cutoff-multiplication operator on the graph space -/

/-- The **cutoff-multiplication operator** `cutoffMul η : H1amb Ω →L H1amb Ω`, encoding the
Leibniz rule `∇(η u) = η ∇u + (∇η) u`: coordinate `0` multiplies by `η`, coordinate `i+1`
sends `U` to `η · U_{i+1} + (∂ᵢη) · U₀`. -/
def cutoffMul {Ω : Set (EuclideanSpace ℝ (Fin d))} {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn Ω η) : H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi
        (Fin.cons ((mulTest h).comp (ContinuousLinearMap.proj 0))
          (fun i => (mulTest h).comp (ContinuousLinearMap.proj i.succ)
            + (mulTestPartial h i).comp (ContinuousLinearMap.proj 0)))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => L2D Ω)).toContinuousLinearMap)

/-- Coordinate `0` of `cutoffMul`: `(cutoffMul η U)₀ = η · U₀`. -/
lemma cutoffMul_apply_zero {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (U : H1amb Ω) :
    (cutoffMul h U) 0 = mulTest h (U 0) := by
  simp only [cutoffMul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_zero, ContinuousLinearMap.proj_apply]

/-- Coordinate `i+1` of `cutoffMul`: `(cutoffMul η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`. -/
lemma cutoffMul_apply_succ {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω η) (U : H1amb Ω) (i : Fin d) :
    (cutoffMul h U) i.succ = mulTest h (U i.succ) + mulTestPartial h i (U 0) := by
  simp only [cutoffMul, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_succ, ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply]

/-! ### The Leibniz product rule and stability of test functions under products -/

/-- The classical Leibniz rule for the `i`-th partial of a product:
`∂ᵢ(η φ) = η ∂ᵢφ + (∂ᵢη) φ`. -/
lemma partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hη : Differentiable ℝ η) (hφ : Differentiable ℝ φ) (i : Fin d) :
    partialD i (fun x => η x * φ x)
      = fun x => η x * partialD i φ x + partialD i η x * φ x := by
  funext x
  simp only [partialD]
  rw [fderiv_fun_mul (hη x) (hφ x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The pointwise product of two test functions is a test function: smoothness is
`ContDiff.mul`, the support of the product sits inside `tsupport φ ⊆ Ω`, and compact
support is inherited from `φ`. -/
lemma isTestFn_mul {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    IsTestFn Ω (fun x => η x * φ x) := by
  refine ⟨hη.1.mul hφ.1, ?_, ?_⟩
  · exact HasCompactSupport.mul_left (f' := φ) (f := η) hφ.2.1
  · exact (closure_mono (Function.support_mul_subset_right η φ)).trans hφ.2.2

/-! ### The keystone: cutoff multiplication sends a graph to the product graph -/

/-- **Keystone (graphs).** The cutoff-multiplication operator sends the graph of a test
function `φ` to the graph of the product `η φ`: `cutoffMul η (graph φ) = graph (η φ)`. This
is the Leibniz rule realised at the level of `L²` classes, and it is what lets `cutoffMul`
extend from test functions to `H₀¹(Ω)` by closure. -/
lemma cutoffMul_testGraph {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) (hφ : IsTestFn Ω φ) :
    cutoffMul hη hφ.testGraph = (isTestFn_mul hη hφ).testGraph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · -- coordinate 0: `η · [φ] = [η φ]`
    rw [cutoffMul_apply_zero, IsTestFn.testGraph_zero, IsTestFn.testGraph_zero]
    apply Lp.ext
    filter_upwards [mulTest_coeFn hη hφ.testCls, hφ.mem_lp.coeFn_toLp,
      (isTestFn_mul hη hφ).mem_lp.coeFn_toLp] with x hx hφx hprod
    rw [hx, show (hφ.testCls x : ℝ) = φ x from hφx]
    exact hprod.symm
  · -- coordinate `i+1`: `η · [∂ᵢφ] + (∂ᵢη) · [φ] = [∂ᵢ(η φ)]`
    rw [cutoffMul_apply_succ, IsTestFn.testGraph_succ, IsTestFn.testGraph_zero,
      IsTestFn.testGraph_succ]
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (mulTest hη (hφ.partialCls i))
        (mulTestPartial hη i hφ.testCls),
      mulTest_coeFn hη (hφ.partialCls i), mulTestPartial_coeFn hη i hφ.testCls,
      (hφ.memLp_partialD i).coeFn_toLp, hφ.mem_lp.coeFn_toLp,
      ((isTestFn_mul hη hφ).memLp_partialD i).coeFn_toLp] with
      x hadd hmt hmtp hpφ hφx hprodp
    rw [hadd, Pi.add_apply, hmt, hmtp]
    change η x * (hφ.partialCls i x : ℝ) + partialD i η x * (hφ.testCls x : ℝ)
      = ((isTestFn_mul hη hφ).partialCls i) x
    rw [show (hφ.partialCls i x : ℝ) = partialD i φ x from hpφ,
      show (hφ.testCls x : ℝ) = φ x from hφx,
      show ((isTestFn_mul hη hφ).partialCls i) x = partialD i (fun y => η y * φ y) x from hprodp,
      congrFun (partialD_mul (hη.1.differentiable (by simp))
        (hφ.1.differentiable (by simp)) i) x]

/-! ### The keystone: cutoff multiplication preserves `H₀¹(Ω)` -/

/-- **Keystone (membership).** The cutoff-multiplication operator maps `H₀¹(Ω)` into
itself. Since `cutoffMul η` is continuous and sends every test-function graph into
`H₀¹(Ω)` (by [`cutoffMul_testGraph`]), it maps the closure `H₀¹(Ω)` into the closed set
`H₀¹(Ω)`. -/
lemma cutoffMul_mem_H01 {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hη : IsTestFn Ω η) {U : H1amb Ω}
    (hU : U ∈ H01 Ω) : cutoffMul hη U ∈ H01 Ω := by
  have hle : (Submodule.span ℝ (testGraphSet Ω)).topologicalClosure
      ≤ Submodule.comap (cutoffMul hη).toLinearMap (H01 Ω) := by
    apply Submodule.topologicalClosure_minimal
    · rw [Submodule.span_le]
      rintro _ ⟨φ, hφ, rfl⟩
      change cutoffMul hη hφ.testGraph ∈ H01 Ω
      rw [cutoffMul_testGraph hη hφ]
      exact (Submodule.le_topologicalClosure _)
        (Submodule.subset_span ⟨_, isTestFn_mul hη hφ, rfl⟩)
    · exact IsClosed.preimage (cutoffMul hη).continuous
        (Submodule.isClosed_topologicalClosure _)
  exact Submodule.mem_comap.mp (hle hU)

/-! ### Weighted energy lower bound from ellipticity -/

/-- **Ellipticity energy bound for an arbitrary `L²` gradient family.** The lower bound of
[`EllipticCoeff.bilin_self_ge`] uses only the `L²` classes, not the weak-gradient
relation, so it holds for any family `g : Fin d → L²(Ω)`:
`λ ∑ᵢ ‖gᵢ‖² ≤ ∑ᵢⱼ ⟪aᵢⱼ gᵢ, gⱼ⟫`. Applied to `gᵢ = ζ · ∂ᵢu` this is the cutoff-weighted
energy lower bound `λ ∫_Ω ζ² |∇u|² ≤ ∫_Ω ζ² ∑ᵢⱼ aᵢⱼ ∂ᵢu ∂ⱼu` driving the Caccioppoli
estimate (Evans, *PDE* 2nd ed., §6.3.1). -/
lemma energy_ge (A : EllipticCoeff d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (g : Fin d → L2D Ω) :
    A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      ≤ ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := by
  have hPint : Integrable (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      (volume.restrict Ω) :=
    (integrable_finsetSum _ (fun i _ => integrable_sq (g i))).const_mul A.lam
  have hpoint : (fun x => A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2)
      ≤ᵐ[volume.restrict Ω] fun x => ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
    (ae_restrict_of_ae A.elliptic).mono (fun x hx => hx (fun i => g i x))
  have hlamS : ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2
      = A.lam * ∑ i : Fin d, ‖g i‖ ^ 2 := by
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => integrable_sq (g i))]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => sq_integral_eq_norm_sq (g i))
  have hRHS : ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫
      = ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
        A.a x i j * (g i x : ℝ) * (g j x : ℝ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => A.integrable_triple i j _ _))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => A.integrable_triple i j _ _)]
    exact Finset.sum_congr rfl (fun j _ => A.inner_actL_eq i j _ _)
  calc A.lam * ∑ i : Fin d, ‖g i‖ ^ 2
      = ∫ x in Ω, A.lam * ∑ i : Fin d, (g i x : ℝ) ^ 2 := hlamS.symm
    _ ≤ ∫ x in Ω, ∑ i : Fin d, ∑ j : Fin d,
          A.a x i j * (g i x : ℝ) * (g j x : ℝ) :=
        integral_mono_ae hPint (integrable_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ => A.integrable_triple i j _ _))) hpoint
    _ = ∑ i : Fin d, ∑ j : Fin d, ⟪A.actL i j (g i), g j⟫ := hRHS.symm

end EllipticDirichlet.Regularity
