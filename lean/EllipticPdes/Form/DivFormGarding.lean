/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.BilinearForm
public import EllipticPdes.Form.DivForm

/-!
# Gårding inequality and Lax-Milgram for divergence-form operators

For a `FullEllipticOp μ` on a real inner product space `E`, the full form on
`H1Graph.H01 μ Ω` satisfies the Gårding inequality
`λ/2 ‖U‖² ≤ B[U, U] + γ ‖u‖²`, where `γ = Op.gardingγ` involves neither the dimension nor the
domain. Adding `m ⟪u, v⟫` with `m ≥ γ` gives a coercive form, and Lax-Milgram then solves the
shifted problem for every continuous functional on `H₀¹`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.garding`: the Gårding inequality.
* `EllipticPdes.DivForm.FullEllipticOp.shiftedForm`: `B[u, v] + m ⟪u, v⟫_{L²}` on `H₀¹`.
* `EllipticPdes.DivForm.FullEllipticOp.shiftedForm_coercive`: coercivity for `m ≥ γ`.
* `EllipticPdes.DivForm.FullEllipticOp.weak_solution`: unique solvability of the shifted problem.
* `EllipticPdes.H1Graph.coercive_of_energy_le`: coercivity from an energy bound and a Poincaré
  bound.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {Ω : Set E}

namespace H1Graph

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Coercivity from an energy bound and a Poincaré bound.** If a bilinear form on a submodule
`S` of the graph space dominates `lam` times the Dirichlet energy `‖∇u‖²` and the function part
is bounded by `CP` times the energy, then the form dominates the graph norm with constant
`lam / (CP + 1)`. -/
theorem coercive_of_energy_le (S : Submodule ℝ (H1Graph μ Ω)) {B : S →L[ℝ] S →L[ℝ] ℝ}
    {lam CP : ℝ} (hlam : 0 < lam) (hCP : 0 ≤ CP)
    (hE : ∀ U : S, lam * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 ≤ B U U)
    (hP : ∀ U : S, ‖fnL (U : H1Graph μ Ω)‖ ^ 2 ≤ CP * ‖gradL (U : H1Graph μ Ω)‖ ^ 2)
    (U : S) : lam / (CP + 1) * ‖U‖ * ‖U‖ ≤ B U U := by
  have hpos : 0 < CP + 1 := by linarith
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 := by
    have hn : ‖U‖ ^ 2 = ‖fnL (U : H1Graph μ Ω)‖ ^ 2 + ‖gradL (U : H1Graph μ Ω)‖ ^ 2 :=
      norm_sq_eq (U : H1Graph μ Ω)
    linarith [hP U, sq ‖U‖]
  calc lam / (CP + 1) * ‖U‖ * ‖U‖
      = lam / (CP + 1) * (‖U‖ * ‖U‖) := by ring
    _ ≤ lam / (CP + 1) * ((CP + 1) * ‖gradL (U : H1Graph μ Ω)‖ ^ 2) := by gcongr
    _ = lam * ‖gradL (U : H1Graph μ Ω)‖ ^ 2 := by field_simp
    _ ≤ B U U := hE U

end H1Graph

namespace DivForm

/-- The Peter-Paul (Young) inequality `B x y ≤ (λ/2) x² + (B²/2λ) y²` for `λ > 0`. -/
lemma young_peterPaul {lam B x y : ℝ} (hlam : 0 < lam) :
    B * x * y ≤ lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 := by
  rw [← sub_nonneg]
  have key : lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 - B * x * y
      = (lam * x - B * y) ^ 2 / (2 * lam) := by field_simp; ring
  rw [key]
  positivity

namespace FullEllipticOp

variable [IsFiniteMeasureOnCompacts μ] (Op : FullEllipticOp μ)

/-- **Gårding inequality.** With `β = λ/2` and `γ = Op.gardingγ`,
`β ‖U‖² ≤ B[U, U] + γ ‖u‖²_{L²}` for every `U ∈ H₀¹(Ω)`. The proof applies Cauchy-Schwarz and
the Peter-Paul inequality once to `⟪b ∇u, u⟫`. -/
theorem garding (Ω : Set E) (U : H1Graph.H01 μ Ω) :
    Op.lam / 2 * ‖U‖ ^ 2 ≤
      Op.formOn Ω (H1Graph.H01 μ Ω) U U + Op.gardingγ * ‖H1Graph.fnL (U : H1Graph μ Ω)‖ ^ 2 := by
  have h := Op.form_self_ge (U : H1Graph μ Ω)
  have hy := young_peterPaul (B := Op.Bsup) (x := ‖H1Graph.gradL (U : H1Graph μ Ω)‖)
    (y := ‖H1Graph.fnL (U : H1Graph μ Ω)‖) Op.lam_pos
  have hn : ‖U‖ ^ 2 = ‖H1Graph.fnL (U : H1Graph μ Ω)‖ ^ 2 +
      ‖H1Graph.gradL (U : H1Graph μ Ω)‖ ^ 2 := H1Graph.norm_sq_eq (U : H1Graph μ Ω)
  rw [FullEllipticOp.formOn_apply, gardingγ, hn]
  linarith

/-- The Gårding inequality with the embedding `H₀¹(Ω) → L²(Ω)` in place of the function part. -/
theorem garding_embL2 (Ω : Set E) (U : H1Graph.H01 μ Ω) :
    Op.lam / 2 * ‖U‖ ^ 2 ≤
      Op.formOn Ω (H1Graph.H01 μ Ω) U U + Op.gardingγ * ‖H1Graph.embL2 μ Ω U‖ ^ 2 :=
  Op.garding Ω U

/-- The shifted form `B[u, v] + m ⟪u, v⟫_{L²}` on `H₀¹(Ω)`, associated to `Lu + m u`. -/
def shiftedForm (Ω : Set E) (m : ℝ) :
    H1Graph.H01 μ Ω →L[ℝ] H1Graph.H01 μ Ω →L[ℝ] ℝ :=
  Op.formOn Ω (H1Graph.H01 μ Ω) +
    m • ((innerSL ℝ).bilinearComp (H1Graph.embL2 μ Ω) (H1Graph.embL2 μ Ω) :
      H1Graph.H01 μ Ω →L[ℝ] H1Graph.H01 μ Ω →L[ℝ] ℝ)

/-- The shifted form is the full form plus `m` times the `L²` pairing. -/
lemma shiftedForm_apply (Ω : Set E) (m : ℝ)
    (U V : H1Graph.H01 μ Ω) :
    Op.shiftedForm Ω m U V =
      Op.formOn Ω (H1Graph.H01 μ Ω) U V +
        m * ⟪H1Graph.embL2 μ Ω U, H1Graph.embL2 μ Ω V⟫ := by
  simp [shiftedForm]

/-- **Shifted coercivity.** For `m ≥ γ` the shifted form is coercive on `H₀¹(Ω)` with constant
`λ/2`; the Gårding inequality already controls the graph norm, so no Poincaré inequality is
needed. -/
theorem shiftedForm_coercive (Ω : Set E) {m : ℝ}
    (hm : Op.gardingγ ≤ m) : IsCoercive (Op.shiftedForm Ω m) := by
  refine ⟨Op.lam / 2, by have := Op.lam_pos; linarith, fun U => ?_⟩
  have hg := Op.garding_embL2 Ω U
  have hmn : Op.gardingγ * ‖H1Graph.embL2 μ Ω U‖ ^ 2 ≤ m * ‖H1Graph.embL2 μ Ω U‖ ^ 2 := by
    gcongr
  rw [shiftedForm_apply, real_inner_self_eq_norm_sq]
  linarith

/-- **Existence and uniqueness for `Lu + m u = f`.** For a shift `m ≥ γ` and every continuous
functional `f` on `H₀¹(Ω)` there is a unique `u ∈ H₀¹(Ω)` with `B_m[u, v] = f v` for all `v`. -/
theorem weak_solution (Ω : Set E) {m : ℝ}
    (hm : Op.gardingγ ≤ m) (f : H1Graph.H01 μ Ω →L[ℝ] ℝ) :
    ∃! u : H1Graph.H01 μ Ω, ∀ v, Op.shiftedForm Ω m u v = f v :=
  (Op.shiftedForm_coercive Ω hm).existsUnique_apply_eq f

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- With no drift and a nonnegative zeroth-order coefficient on `Ω`, the lower-order form is
nonnegative on the diagonal. -/
lemma lowerForm_self_nonneg (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) (U : H1Graph μ Ω) : 0 ≤ Op.lowerForm Ω U U := by
  rw [lowerForm_eq_integral]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hb, hc] with x hbx hcx
  simp only [hbx, inner_zero_left, zero_mul, zero_add, Pi.zero_apply]
  rw [mul_assoc]
  exact mul_nonneg hcx (mul_self_nonneg _)

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ] in
/-- With no drift and a nonnegative zeroth-order coefficient on `Ω`, the full form dominates
`λ ‖∇u‖²`. -/
lemma form_self_ge_of_nonneg_restrict (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) (U : H1Graph μ Ω) :
    Op.lam * ‖H1Graph.gradL U‖ ^ 2 ≤ Op.form Ω U U := by
  rw [form_apply]
  linarith [Op.toEllipticCoeff.form_self_ge Ω U, Op.lowerForm_self_nonneg hb hc U]

/-- **Coercivity from a Poincaré inequality.** With no drift, a nonnegative zeroth-order
coefficient and the Poincaré inequality `‖u‖² ≤ CP ‖∇u‖²` on `H₀¹(Ω)`, the form dominates the
graph norm with constant `λ / (CP + 1)` and needs no shift. -/
theorem form_coercive_of_poincare (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) {CP : ℝ} (hCP : 0 ≤ CP)
    (hP : ∀ U ∈ H1Graph.H01 μ Ω,
      ‖H1Graph.fnL U‖ ^ 2 ≤ CP * ‖H1Graph.gradL U‖ ^ 2) (U : H1Graph.H01 μ Ω) :
    Op.lam / (CP + 1) * ‖U‖ * ‖U‖ ≤ Op.formOn Ω (H1Graph.H01 μ Ω) U U :=
  H1Graph.coercive_of_energy_le (H1Graph.H01 μ Ω) Op.lam_pos hCP
    (fun V => Op.form_self_ge_of_nonneg_restrict hb hc V) (fun V => hP V V.2) U

end FullEllipticOp

end DivForm

end EllipticPdes
