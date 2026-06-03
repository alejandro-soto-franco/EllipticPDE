import EllipticDirichlet.Poincare.Density
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# The divergence-form bilinear form (dependency-chain step 5)

We treat the symmetric, transport-free, zeroth-order-free case first: the Dirichlet
(Poisson) form `B[U, V] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²}`, i.e. the coefficient matrix is the
identity and `c = 0`. In the graph encoding of `Sobolev/Basic.lean` the `i`-th weak
partial of `U ∈ H₀¹(Ω)` is the coordinate `U (i.succ)`, so

  `B[U, V] = ∑ i, ⟪(↑U) i.succ, (↑V) i.succ⟫`.

* **Continuity** (`β = d`): each coordinate norm is bounded by the ambient `H¹` norm.
* **Coercivity** (`α = 1 / (C_P + 1)`): `B[U, U] = ∑ᵢ ‖∂ᵢu‖²` is the Dirichlet energy,
  and the density Poincaré inequality `poincare_H01` controls the function part `‖u‖²`
  by that energy, so `B` dominates the full `H¹` norm.

This is the `γ = 0` case of Guo §VII.3.4: coercivity is immediate from the energy
identity plus Poincaré, with no Gårding absorption. It is exactly the hypothesis the
Lax-Milgram theorem (M6) consumes. The general elliptic matrix `A` and `c ≥ 0` follow the
same shape with `A`'s ellipticity constant in place of `1` (cf. DeGiorgi
`WeakFormulation/CoefficientOperator.lean`).
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet

open EllipticDirichlet.Sobolev EllipticDirichlet.Poincare

variable {d : ℕ}

/-- The Dirichlet bilinear form as a bare bilinear map on `H₀¹(Ω)`:
`B[U, V] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫_{L²}`. -/
def dirichletBilinₗ (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →ₗ[ℝ] (H01 Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V => ∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_left,
          Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_left,
          smul_eq_mul, Finset.mul_sum])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_right,
          Finset.sum_add_distrib])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_right,
          smul_eq_mul, Finset.mul_sum])

/-- The Dirichlet bilinear form on `H₀¹(Ω)` as a bounded (continuous) bilinear form,
with operator-norm bound `d`. -/
def dirichletBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (dirichletBilinₗ Ω).mkContinuous₂ (d : ℝ) (by
    intro U V
    simp only [dirichletBilinₗ, LinearMap.mk₂_apply]
    calc ‖∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫‖
        ≤ ∑ i : Fin d, ‖⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ * ‖(V : H1amb Ω) i.succ‖ :=
          Finset.sum_le_sum (fun i _ => norm_inner_le_norm _ _)
      _ ≤ ∑ _i : Fin d, ‖U‖ * ‖V‖ :=
          Finset.sum_le_sum (fun i _ => by
            gcongr
            · exact PiLp.norm_apply_le _ _
            · exact PiLp.norm_apply_le _ _)
      _ = (d : ℝ) * ‖U‖ * ‖V‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc])

@[simp] lemma dirichletBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    dirichletBilin Ω U V = ∑ i : Fin d, ⟪(U : H1amb Ω) i.succ, (V : H1amb Ω) i.succ⟫ := by
  simp only [dirichletBilin, LinearMap.mkContinuous₂_apply, dirichletBilinₗ, LinearMap.mk₂_apply]

/-- The Dirichlet energy identity: `B[U, U] = ∑ᵢ ‖∂ᵢu‖²`. -/
lemma dirichletBilin_self (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    dirichletBilin Ω U U = ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 := by
  rw [dirichletBilin_apply]
  exact Finset.sum_congr rfl (fun i _ => real_inner_self_eq_norm_sq _)

/-- **Coercivity of the Dirichlet form.** Given the test-function Poincaré bound with
constant `C_P ≥ 0`, the Dirichlet form is coercive on `H₀¹(Ω)` with constant
`1 / (C_P + 1)`: the density Poincaré inequality controls the function part by the
Dirichlet energy, so `B[U, U]` dominates the full `H¹` norm. -/
theorem dirichletBilin_coercive (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    IsCoercive (dirichletBilin Ω) := by
  have hpos : (0 : ℝ) < CP + 1 := by linarith
  refine ⟨1 / (CP + 1), by positivity, ?_⟩
  intro U
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  -- The Dirichlet energy is `S`.
  have hBUU : dirichletBilin Ω U U = S := dirichletBilin_self Ω U
  -- The full `H¹` norm splits into function part plus `S`.
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  -- Density Poincaré controls the function part by the energy.
  have hpoin : ‖(U : H1amb Ω) 0‖ ^ 2 ≤ CP * S :=
    poincare_H01 CP hbase U.2
  -- Hence `‖U‖² ≤ (C_P + 1) · S`, i.e. `(1 / (C_P + 1)) ‖U‖² ≤ B[U, U]`.
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * S := by
    have : ‖U‖ ^ 2 ≤ (CP + 1) * S := by rw [hnorm]; nlinarith [hpoin]
    nlinarith [this]
  rw [hBUU, mul_assoc]
  calc 1 / (CP + 1) * (‖U‖ * ‖U‖)
      ≤ 1 / (CP + 1) * ((CP + 1) * S) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = S := by rw [← mul_assoc, one_div_mul_cancel hpos.ne', one_mul]

end EllipticDirichlet
