/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.Slab
public import EllipticPdes.Sobolev.Graph

/-!
# Poincaré inequality on `H₀¹` of a bounded set, over a general inner product space

For a bounded `Ω` in a nontrivial finite-dimensional real inner product space `E` with an
additive Haar measure `μ`, the function part of every `U ∈ H1Graph.H01 μ Ω` is controlled by its
gradient part. A unit vector `v` and the functional `ℓ = ⟪v, ·⟫` put `Ω` in a slab
`a < ℓ x < b`, the slab inequality bounds `∫ φ²` for test functions, and the inequality extends
to `H₀¹(Ω)` because it defines a closed condition on the graph space.

## Main declarations

* `EllipticPdes.H1Graph.poincare_testGraphₗ_of_subset_slab`: the inequality for test graphs.
* `EllipticPdes.H1Graph.poincare_H01_of_bounded`: the inequality on `H₀¹` of a bounded set.
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.H1Graph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Set E}

section FiniteOnCompacts

variable [IsFiniteMeasureOnCompacts μ]

/-- The squared function part of a test graph is `∫ φ²` over `Ω`. -/
lemma norm_sq_fnL_testGraphₗ (φ : testFunctions Ω) :
    ‖fnL (testGraphₗ μ Ω φ)‖ ^ 2 = ∫ x in Ω, (φ : E → ℝ) x ^ 2 ∂μ := by
  rw [fnL_testGraphₗ, ← real_inner_self_eq_norm_sq, fnCls, inner_toLp_toLp]
  simp [sq]

/-- The squared gradient part of a test graph is `∫ ‖∇φ‖²` over `Ω`. -/
lemma norm_sq_gradL_testGraphₗ (φ : testFunctions Ω) :
    ‖gradL (testGraphₗ μ Ω φ)‖ ^ 2 = ∫ x in Ω, ‖gradient (φ : E → ℝ) x‖ ^ 2 ∂μ := by
  rw [gradL_testGraphₗ, ← real_inner_self_eq_norm_sq, gradCls, inner_toLp_toLp]
  simp

end FiniteOnCompacts

variable [μ.IsAddHaarMeasure]

/-- **Poincaré inequality for test graphs in a slab.** If `ℓ v = 1`, `‖v‖ = 1` and `Ω` lies in
the slab `a < ℓ x < b`, then `‖u‖² ≤ (b - a)² / 2 · ‖∇u‖²` for the graph of every test
function `φ`. -/
theorem poincare_testGraphₗ_of_subset_slab (ℓ : E →L[ℝ] ℝ) {v : E} (hv : ℓ v = 1) (hv1 : ‖v‖ = 1)
    {a b : ℝ} (hs : Ω ⊆ ℓ ⁻¹' Ioo a b) (φ : testFunctions Ω) :
    ‖fnL (testGraphₗ μ Ω φ)‖ ^ 2 ≤ (b - a) ^ 2 / 2 * ‖gradL (testGraphₗ μ Ω φ)‖ ^ 2 := by
  have hφ := φ.2
  have hsub := hφ.2.2
  have hp := Poincare.integral_sq_le_of_tsupport_subset_slab (μ := μ)
    (hφ.1.of_le (by exact_mod_cast le_top)) hφ.2.1 ℓ hv (hsub.trans hs)
  have key : ∀ f : E → ℝ, (∀ x ∉ tsupport (φ : E → ℝ), f x = 0) →
      ∫ x in Ω, f x ∂μ = ∫ x, f x ∂μ := fun f hf =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hf x fun h => hx (hsub h)
  rw [norm_sq_fnL_testGraphₗ, norm_sq_gradL_testGraphₗ,
    key (fun x => (φ : E → ℝ) x ^ 2) fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy],
    key (fun x => ‖gradient (φ : E → ℝ) x‖ ^ 2) fun y hy => by
      simp [gradient, fderiv_of_notMem_tsupport ℝ hy]]
  refine hp.trans (mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun x => ?_) (by positivity))
  · have hk : HasCompactSupport fun x => fderiv ℝ (φ : E → ℝ) x v ^ 2 :=
      (hasCompactSupport_fderiv_apply_of_mem hφ v).comp_left (g := fun r : ℝ => r ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport
      ((continuous_fderiv_apply_of_mem hφ v).pow 2) hk
  · have hk : HasCompactSupport fun x => ‖gradient (φ : E → ℝ) x‖ ^ 2 :=
      (hasCompactSupport_gradient_of_mem hφ).norm.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport
      ((continuous_gradient_of_mem hφ).norm.pow 2) hk
  · have h := abs_real_inner_le_norm v (gradient (φ : E → ℝ) x)
    rw [hv1, one_mul, inner_gradient_right] at h
    calc fderiv ℝ (φ : E → ℝ) x v ^ 2 = |fderiv ℝ (φ : E → ℝ) x v| ^ 2 := (sq_abs _).symm
      _ ≤ ‖gradient (φ : E → ℝ) x‖ ^ 2 := by gcongr

/-- **Poincaré inequality on `H₀¹` of a bounded set.** Some constant `C ≥ 0` controls the function
part of every element of `H₀¹(Ω)` by its gradient part, in any dimension at least one. -/
theorem poincare_H01_of_bounded [Nontrivial E] (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U ∈ H01 μ Ω, ‖fnL U‖ ^ 2 ≤ C * ‖gradL U‖ ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  set v : E := ‖x₀‖⁻¹ • x₀
  have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hx₀
  have hv : innerSL ℝ v v = 1 := by simp [hv1]
  obtain ⟨R, hR⟩ := hΩb.exists_norm_le
  have hslab : Ω ⊆ innerSL ℝ v ⁻¹' Ioo (-R - 1) (R + 1) := fun x hx => by
    have h := abs_real_inner_le_norm v x
    rw [hv1, one_mul] at h
    have := hR x hx
    rw [mem_preimage, innerSL_apply_apply, mem_Ioo]
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  refine ⟨(R + 1 - (-R - 1)) ^ 2 / 2, by positivity, fun U hU => ?_⟩
  have hcl : IsClosed
      {U : H1Graph μ Ω | ‖fnL U‖ ^ 2 ≤ (R + 1 - (-R - 1)) ^ 2 / 2 * ‖gradL U‖ ^ 2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact H01_subset_of_isClosed hcl
    (fun φ => poincare_testGraphₗ_of_subset_slab (innerSL ℝ v) hv hv1 hslab φ) hU

end EllipticPdes.H1Graph
