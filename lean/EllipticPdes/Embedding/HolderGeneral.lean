/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.HolderOfGradClosed
public import EllipticPdes.Embedding.SobolevLadder

/-!
# Hölder continuity at a general base exponent

`EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed` runs the ladder from `L²` and reads
the Hölder exponent off Morrey's inequality at the exponent the ladder reaches. Morrey is already
stated for every exponent above the dimension, and the rung count and the landing exponent are
already free there, so the base exponent is the only thing left at `2`. This file frees it, which
is the second case of Evans, *Partial Differential Equations*, §5.6.3 Theorem 6, and of Guo,
*Partial Differential Equations*, Theorem IV.2.3, at the exponent each quantifies over.

## Landing exponent

Running `s` rungs from `p₀` lands at the reciprocal `1/p₀ - s/d`, and Morrey at that exponent
gives the Hölder exponent `1 - d/P = s + 1 - d/p₀`. At `s = ⌊d/p₀⌋` that is the
`⌊n/p⌋ + 1 - n/p` of the cited statements. When `d/p₀` is an integer the reciprocal reaches `0`,
the ladder reaches every finite exponent, and the Hölder exponent is free in `(0,1)`, which is
the other case those statements separate out.

## Main declarations

* `EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general`: the Hölder clause at a
  general base exponent.
* `EllipticPdes.Embedding.morreyExponent_eq_ladder`: the exponent it lands on is the one the
  cited statements name.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
Guo, *Partial Differential Equations*, Theorem IV.2.3 case (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Hölder clause at a general base exponent.** The ladder run for `s` rungs from `L^{p₀}`
lands at any `P` the reciprocal relation `1/p₀ - s/d ≤ 1/P` admits, and Morrey at `P > d` reads
off the exponent `1 - d/P`. -/
theorem exists_holderOnWith_of_gradClosed_general (hd : 1 < d) (c : EuclideanSpace ℝ (Fin d))
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict (Metric.ball c R)))
    {s : ℕ} {P : ℝ≥0} (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P)
    (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹)
    (i : ι) (hi : dep i + 1 + s ≤ m) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  have hd0 : 0 < d := by omega
  have hp₀E : (1 : ℝ≥0∞) ≤ (p₀ : ℝ≥0∞) := by exact_mod_cast hp₀
  -- The gradient coordinates reach `L^P` on the inner ball.
  have hgradP : ∀ k, MemLp (F (nxt i k)) (ENNReal.ofReal (P : ℝ))
      (volume.restrict (Metric.ball c r)) := fun k => by
    rw [ENNReal.ofReal_coe_nnreal]
    exact memLp_of_gradClosed_general hd c hp₀ hdep s hsd hp₀P hPs hr hrR hgrad hmem
      (nxt i k) (by have := hdep i k; omega)
  -- The member itself is integrable there.
  have hFint : IntegrableOn (F i) (Metric.ball c r) volume :=
    ((hmem i (by omega)).mono_measure
      (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl)).integrable hp₀E
  have hgradr : HasWeakGradOn (Metric.ball c r) (F i) (fun k => F (nxt i k)) :=
    (hgrad i (by omega)).mono (Metric.ball_subset_ball hrR.le)
  obtain ⟨C, hC⟩ := morrey_ball hd0 hPd c hr
  obtain ⟨w, hwae, hwhol⟩ := hC (F i) (fun k => F (nxt i k)) hFint hgradP hgradr
  exact ⟨w, hwae, ⟨_, hwhol⟩⟩

/-- **Agreement of the ladder's exponent with the cited one.** At the landing
reciprocal `1/P = 1/p₀ - s/d`, Morrey's exponent is `s + 1 - d/p₀`, which at `s = ⌊d/p₀⌋` is the
`⌊n/p⌋ + 1 - n/p` of Evans §5.6.3 Theorem 6 and Guo Theorem IV.2.3. -/
theorem morreyExponent_eq_ladder (hd : 0 < d) {p₀ P : ℝ≥0} {s : ℕ}
    (hp₀ : 0 < (p₀ : ℝ)) (hPd : (d : ℝ) ≤ (P : ℝ))
    (hP : (P : ℝ)⁻¹ = (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹) :
    ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ) = (s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hP0 : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le hdR hPd
  have hnn : (0 : ℝ) ≤ 1 - (d : ℝ) / (P : ℝ) := by
    rw [sub_nonneg, div_le_one hP0]
    exact hPd
  have hval : 1 - (d : ℝ) / (P : ℝ) = (s : ℝ) + 1 - (d : ℝ) / (p₀ : ℝ) := by
    rw [div_eq_mul_inv, hP]
    field_simp
    ring
  rw [morreyExponent, Real.coe_toNNReal _ hnn, hval]

/-- **An exponent with a prescribed Morrey exponent.** For `γ ∈ (0, 1)` the exponent
`P = d/(1 - γ)` exceeds `d` and has Morrey exponent `γ`. -/
theorem exists_nnreal_morreyExponent_eq (hd : 0 < d) {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ P : ℝ≥0, (d : ℝ) < (P : ℝ) ∧ morreyExponent d (P : ℝ) = γ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hγ1R : ((γ : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hγ1
  have hγ0R : (0 : ℝ) < ((γ : ℝ≥0) : ℝ) := by exact_mod_cast hγ0
  have hden : (0 : ℝ) < 1 - (γ : ℝ) := by linarith
  have hPcoe : (((d : ℝ) / (1 - (γ : ℝ))).toNNReal : ℝ) = (d : ℝ) / (1 - (γ : ℝ)) :=
    Real.coe_toNNReal _ (by positivity)
  have hPd : (d : ℝ) < ((d : ℝ) / (1 - (γ : ℝ))).toNNReal := by
    rw [hPcoe, lt_div_iff₀ hden]
    nlinarith
  refine ⟨_, hPd, NNReal.coe_injective ?_⟩
  rw [coe_morreyExponent hPd hd, hPcoe]
  field_simp
  ring

/-- **Guo's free Hölder exponent in even dimension.** When `d/2` is an integer, which at `p = 2`
is Guo's case `n/p ∈ ℕ`, the ladder reaches every finite exponent, so the Hölder exponent may be
any value in `(0,1)`. In odd dimension the reciprocal `1/2 - ⌊d/2⌋/d = 1/(2d)` caps the exponent
at `2d` and the Hölder exponent at `1/2`, which is Guo's other case. -/
theorem exists_holderOnWith_of_gradClosed_even (hd : 0 < d) (hdeven : 2 * (d / 2) = d)
    (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R)))
    {γ : ℝ≥0} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (i : ι) (hi : dep i + 1 + d / 2 ≤ m) :
    ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M γ w (Metric.ball c r) := by
  obtain ⟨P, hPd, hγP⟩ := exists_nnreal_morreyExponent_eq hd hγ0 hγ1
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
  have hdR : (0 : ℝ) < d := by linarith
  have hhalf : ((d / 2 : ℕ) : ℝ) * (d : ℝ)⁻¹ = 2⁻¹ := by
    have hn : ((d / 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hR : (d : ℝ) = 2 * ((d / 2 : ℕ) : ℝ) := by exact_mod_cast hdeven.symm
    rw [hR, mul_inv]
    field_simp
  obtain ⟨w, hwae, M, hwhol⟩ := exists_holderOnWith_of_gradClosed_general (by omega) c hr hrR
    (p₀ := 2) one_le_two hdep hgrad hmem (s := d / 2) (P := P)
    (by push_cast; exact_mod_cast hdeven.le) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) hPd
    (by rw [NNReal.coe_ofNat, hhalf, sub_self]; positivity) i hi
  exact ⟨w, hwae, M, hγP ▸ hwhol⟩

end EllipticPdes.Embedding
