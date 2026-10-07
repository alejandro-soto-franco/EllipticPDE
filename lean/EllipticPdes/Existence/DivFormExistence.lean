/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.DivFormGarding
public import EllipticPdes.Poincare.GraphBounded

/-!
# Existence for divergence-form operators on a bounded set

For an operator with no drift and a nonnegative zeroth-order coefficient on a bounded set `Ω`,
the form on `H1Graph.H01 μ Ω` is coercive without a shift, by the Poincaré inequality. Lax-Milgram
then solves `B[u, v] = ⟪f, v⟫_{L²}` for every `f ∈ L²(Ω)`, with the bound
`‖u‖ ≤ (CP + 1) / λ · ‖f‖`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.weak_solution_of_nonneg_zeroth_of_bounded`: existence,
  uniqueness and the a-priori bound.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

/-- **Existence, uniqueness and the a-priori bound on a bounded set, `L²` datum.** If the drift
vanishes and the zeroth-order coefficient is nonnegative on `Ω`, there is a constant `CP ≥ 0`,
depending only on `Ω`, such that for every `f ∈ L²(Ω)` the problem `B[u, v] = ⟪f, v⟫` has a
unique solution `u ∈ H₀¹(Ω)`, and every solution obeys `‖u‖ ≤ (CP + 1) / λ · ‖f‖`. -/
theorem weak_solution_of_nonneg_zeroth_of_bounded [Nontrivial E] (Op : FullEllipticOp μ)
    (hΩb : Bornology.IsBounded Ω) (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      (∃! u : H1Graph.H01 μ Ω, ∀ v,
        Op.formOn Ω (H1Graph.H01 μ Ω) u v = ⟪f, H1Graph.embL2 μ Ω v⟫) ∧
      ∀ u : H1Graph.H01 μ Ω,
        (∀ v, Op.formOn Ω (H1Graph.H01 μ Ω) u v = ⟪f, H1Graph.embL2 μ Ω v⟫) →
          ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  obtain ⟨CP, hCP, hP⟩ := H1Graph.poincare_H01_of_bounded (μ := μ) hΩb
  have hα : 0 < Op.lam / (CP + 1) := div_pos Op.lam_pos (by linarith)
  have hco := Op.form_coercive_of_poincare hb hc hCP hP
  refine ⟨CP, hCP, fun f => ?_⟩
  set F : H1Graph.H01 μ Ω →L[ℝ] ℝ := (innerSL ℝ f).comp (H1Graph.embL2 μ Ω)
  have hF : ‖F‖ ≤ ‖f‖ := F.opNorm_le_bound (norm_nonneg f) fun v =>
    (abs_real_inner_le_norm _ _).trans <| by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (H1Graph.norm_embL2_le v) (norm_nonneg f)
  have hex := IsCoercive.existsUnique_apply_eq (B := Op.formOn Ω (H1Graph.H01 μ Ω))
    ⟨_, hα, hco⟩ F
  refine ⟨hex, fun u hu => ?_⟩
  have h := norm_weak_solution_le hα hco (f := F) hu
  rw [inv_div] at h
  have := Op.lam_pos
  exact h.trans (by gcongr)

end EllipticPdes.DivForm.FullEllipticOp
