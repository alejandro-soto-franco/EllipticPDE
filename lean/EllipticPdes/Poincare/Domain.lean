/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Poincare.Fubini

/-!
# Full Poincaré inequality on the domain (dependency-chain step 3)

Average the `n` directional bounds from `poincare_slice_box` to obtain the
domain Poincaré inequality. Each coordinate direction `i` of the box contributes
a bound `∫_Ω u² ≤ c i * ∫_Ω (∂_i u)²`; summing over the `n` directions and
dividing by `n` gives `∫_Ω u² ≤ (1 / n) * ∑_i c i * ∫_Ω (∂_i u)²`. The resulting
constant is the domain constant `C_P` (for equal side lengths `c i = L² / 2` this
is `L² / (2 n)`, matching the diameter-based bound).
-/

open MeasureTheory

namespace EllipticPdes.Poincare

/-- Domain Poincaré inequality by averaging the per-direction slice bounds.
Given, for each of the `n` coordinate directions `i`, a Poincaré bound
`∫_Ω u² ≤ c i * ∫_Ω (∂_i u)²`, the `L²` norm of `u` over the box is controlled by
the average of the `n` directional Dirichlet energies. -/
theorem poincare_domain
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Ω : Set α}
    {n : ℕ} (hn : 0 < n) {u : α → ℝ} {d : Fin n → α → ℝ} {c : Fin n → ℝ}
    (hslice : ∀ i, (∫ x in Ω, (u x) ^ 2 ∂μ) ≤ c i * ∫ x in Ω, (d i x) ^ 2 ∂μ) :
    (∫ x in Ω, (u x) ^ 2 ∂μ)
      ≤ (1 / n) * ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set L := ∫ x in Ω, (u x) ^ 2 ∂μ with hL
  have hsum : (n : ℝ) * L ≤ ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := by
    calc (n : ℝ) * L = ∑ _i : Fin n, L := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i, c i * ∫ x in Ω, (d i x) ^ 2 ∂μ := Finset.sum_le_sum fun i _ => hslice i
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hnpos, mul_comm L (n : ℝ)]
  exact hsum

end EllipticPdes.Poincare
