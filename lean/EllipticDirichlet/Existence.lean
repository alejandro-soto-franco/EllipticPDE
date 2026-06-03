import EllipticDirichlet.BilinearForm

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

namespace EllipticDirichlet

open EllipticDirichlet.Sobolev EllipticDirichlet.Poincare

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

end EllipticDirichlet
