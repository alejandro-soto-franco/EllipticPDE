/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.BilinearForm
import EllipticPdes.Poincare.BoxSlice

/-!
# Existence and uniqueness via Lax-Milgram (dependency-chain step 6)

On the Hilbert space `H₀¹(Ω)` the Dirichlet bilinear form is bounded (continuous) and,
given the Poincaré inequality, coercive (`dirichletBilin_coercive`). Mathlib's Lax-Milgram
theorem `IsCoercive.continuousLinearEquivOfBilin` then yields, for every continuous linear
functional `f` on `H₀¹(Ω)`, a unique weak solution `u` of `B[u, v] = f v` for all `v`.

This is the abstract existence-and-uniqueness statement. The elliptic right-hand side
`f ∈ L²(Ω)` enters as the continuous functional `v ↦ ∫_Ω f · v` (continuous by
Cauchy-Schwarz, the `L² ⊂ H⁻¹` embedding), so the classical Poisson-Dirichlet problem is
the instance with that functional.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

open EllipticPdes.Sobolev EllipticPdes.Poincare

variable {d : ℕ}

/-- **Existence and uniqueness of the weak solution (Lax-Milgram).** Given the
test-function Poincaré bound with constant `C_P ≥ 0`, for every continuous linear
functional `f` on `H₀¹(Ω)` there is a unique `u ∈ H₀¹(Ω)` solving the weak Dirichlet
problem `B[u, v] = f v` for all `v ∈ H₀¹(Ω)`, where `B` is the Dirichlet form
`B[u, v] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫`. -/
theorem dirichlet_weak_solution
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, dirichletBilin Ω u v = f v := by
  have hco : IsCoercive (dirichletBilin Ω) := dirichletBilin_coercive Ω CP hCP hbase
  -- Riesz representative of `f`: a vector `g` with `⟪g, w⟫ = f w`.
  have hgrep : ∀ w : H01 Ω,
      ⟪(InnerProductSpace.toDual ℝ (H01 Ω)).symm f, w⟫ = f w :=
    fun w => InnerProductSpace.toDual_symm_apply
  set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hg
  -- The Lax-Milgram equivalence inverts `g` to the solution.
  refine ⟨hco.continuousLinearEquivOfBilin.symm g, ?_, ?_⟩
  · -- existence: `B[symm g, v] = ⟪equiv (symm g), v⟫ = ⟪g, v⟫ = f v`.
    intro v
    rw [← hco.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hgrep]
  · -- uniqueness: any solution `u` has `⟪equiv u, w⟫ = f w = ⟪g, w⟫`, so `equiv u = g`.
    intro u hu
    apply hco.continuousLinearEquivOfBilin.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    refine ext_inner_right (𝕜 := ℝ) (fun w => ?_)
    rw [hco.continuousLinearEquivOfBilin_apply, hu w, ← hgrep w]

/-- **The a-priori estimate for the weak solution (Poisson form).** Under the hypotheses
of [`dirichlet_weak_solution`], any weak solution obeys `‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with the
coercivity constant `α = 1 / (C_P + 1)`, i.e. `‖u‖_{H₀¹} ≤ (C_P + 1) ‖f‖`. -/
theorem dirichlet_weak_solution_bound
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    {f : H01 Ω →L[ℝ] ℝ} {u : H01 Ω}
    (hu : ∀ v : H01 Ω, dirichletBilin Ω u v = f v) :
    ‖u‖ ≤ (CP + 1) * ‖f‖ := by
  have h := norm_weak_solution_le (α := 1 / (CP + 1)) (by positivity)
    (dirichletBilin_coercive_const Ω CP hCP hbase) hu
  rwa [one_div, inv_inv] at h

/-- **Unconditional existence, uniqueness, and a-priori bound on an open coordinate
box.** Specialising `dirichlet_weak_solution` to the box `∏ₖ (aₖ, bₖ)`, the test-function
Poincaré hypothesis is discharged from the box geometry: the per-direction slice bound
`Poincare.slice_bound_euclBox` (which rests on the one-dimensional/Fubini bound
`Poincare.poincare_box_dir`) is averaged by `Poincare.poincare_testfn` into the
graph-coordinate bound with constant `C_P = C / (n + 1)`. So for every continuous
functional `f` on `H₀¹` of the box there is a unique weak solution of `B[u, v] = f v`,
satisfying the Lax-Milgram estimate `‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with coercivity constant
`α = 1 / (C / (n + 1) + 1)`, all carrying no abstract Poincaré input. This is the box
instance of Theorem `thm: main` for the Poisson form. -/
theorem dirichlet_weak_solution_euclBox {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (hab : ∀ k, a k ≤ b k) (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (f : H01 (euclBox a b) →L[ℝ] ℝ) :
    (∃! u : H01 (euclBox a b),
      ∀ v : H01 (euclBox a b), dirichletBilin (euclBox a b) u v = f v)
    ∧ ∀ u : H01 (euclBox a b),
        (∀ v : H01 (euclBox a b), dirichletBilin (euclBox a b) u v = f v) →
          ‖u‖ ≤ (C / (n + 1) + 1) * ‖f‖ := by
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbase : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ),
      ‖(h.testGraph 0 : L2D (euclBox a b))‖ ^ 2
        ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
    fun {_φ} h => testfn_bound_euclBox hab hC h
  have hCP : 0 ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  refine ⟨dirichlet_weak_solution (euclBox a b) (C / (n + 1)) hCP hbase f, ?_⟩
  intro u hu
  exact dirichlet_weak_solution_bound (euclBox a b) (C / (n + 1)) hCP hbase hu

end EllipticPdes
