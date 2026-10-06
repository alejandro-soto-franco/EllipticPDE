/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.SobolevLadder
public import EllipticPdes.Embedding.SmoothOfGradClosed
public import EllipticPdes.Embedding.ClassicalDeriv

/-!
# Hölder regularity of finite order from a bounded supply of weak derivatives

Guo's Sobolev embedding (Guo, *Partial Differential Equations*, Theorem IV.2.3) has two cases.
The first raises the exponent, and `EllipticPdes.Embedding.memLp_of_gradClosed_fullStep` runs it.
The second reads a bounded supply of weak derivatives as classical ones: for `u ∈ W^{m,p}(Ω)`
with `m > n/p`, the conclusion is `u ∈ C^{m-1-⌊n/p⌋, γ}(Ω)`. This file proves the second case at
`p = 2`, locally, for a family closed under weak differentiation as far as `m`.

## Order the supply pays for

The supply is spent in three places. Morrey asks for the weak gradient, so one order goes there;
the ladder takes `⌊d/2⌋` more raising that gradient from `L²` to `L^{2d}`; and reading the `n`-th
classical derivative asks the same of every index `n` levels up. So an index of depth `dep i`
reaches `C^n` while `dep i + n + 1 + ⌊d/2⌋ ≤ m`, and at `dep i = 0` that is
`n = m - 1 - ⌊d/2⌋`, which is Guo's order exactly.

## Hölder exponent

The ladder lands on `L^{2d}` and `EllipticPdes.Embedding.morrey_ball` reads off `1 - d/(2d)`, so
the exponent is `1/2` in every dimension. For `d` odd this is Guo's `⌊d/2⌋ + 1 - d/2` on the
nose. For `d` even `d/2` is an integer, Guo's statement leaves `γ` free in `(0, 1)`, and `1/2` is
one admissible choice: the ladder's landing reciprocal is `0` there, so every finite exponent is
reached and `2d` is the one this file fixes.

## Main declarations

* `EllipticPdes.Embedding.morreyExponent_two_mul`: the landing exponent is `1/2`.
* `EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed`: representatives of class
  `C^{n, 1/2}`, for every order the supply pays for, together with the identification of the
  family's entries as their classical partial derivatives.

## References

Guo, *Partial Differential Equations*, Theorem IV.2.3.
Evans, *Partial Differential Equations* (2nd ed.), §5.6.3.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Classical derivatives of finite order from a bounded supply of weak ones.** Let `F` assign a
function to each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on
`Metric.ball c R`, and let `dep` record how far an index sits above the root. If every index of
depth at most `m` lies in `L²` there and every index of depth below `m` has its weak gradient in
the family, then on any smaller concentric ball each index has a representative of class `C^n`
whenever `dep i + n + 1 + ⌊d/2⌋ ≤ m`, and that representative is Hölder-`1/2` as soon as
`dep i + 1 + ⌊d/2⌋ ≤ m`.

The proof is the one `EllipticPdes.Embedding.contDiffOn_of_gradClosed` takes, run against a
supply that runs out. The ladder raises the weak gradient of a qualifying index to `L^{2d}`,
Morrey converts that into a Hölder representative, and a continuous function with a continuous
weak gradient is classically differentiable, so an induction on the order reads the family as
`C^n` with no further shrinking of the ball. Each induction step spends one order, which is what
the depth condition records.

The last component states what the family means: on the inner ball the classical derivative of
`v i` is the tuple of the `v (nxt i k)`, so an entry of depth `n` is the order-`n` classical
partial derivative of the root and the Hölder bound above is a bound on that derivative. -/
theorem contDiffOn_holder_of_gradClosed (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    {nxt : ι → Fin d → ι} {dep : ι → ℕ} {m : ℕ} (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1)
    (hgrad : ∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) :
    ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, dep i + 1 + d / 2 ≤ m → v i =ᵐ[volume.restrict (Metric.ball c r)] F i) ∧
      (∀ i, dep i + 1 + d / 2 ≤ m →
        ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) (v i) (Metric.ball c r)) ∧
      (∀ (n : ℕ) (i : ι), dep i + n + 1 + d / 2 ≤ m →
        ContDiffOn ℝ (n : ℕ) (v i) (Metric.ball c r)) ∧
      (∀ i, dep i + 2 + d / 2 ≤ m → ∀ y ∈ Metric.ball c r,
        HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp : (d : ℝ) < 2 * (d : ℝ) := by linarith
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  have hFint : ∀ i, dep i ≤ m → IntegrableOn (F i) (Metric.ball c r) volume := fun i hi =>
    ((hmem i hi).mono_measure (Measure.restrict_mono hsub le_rfl)).integrable (by norm_num)
  -- The ladder lifts every gradient the supply reaches to `L^{2d}`, and Morrey gives each
  -- member above it a Hölder representative.
  obtain ⟨C, hC⟩ := morrey_ball hd hp c hr
  have hex : ∀ i, dep i + 1 + d / 2 ≤ m → ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
      w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
        ∃ M : ℝ≥0, HolderOnWith M (1 / 2 : ℝ≥0) w (Metric.ball c r) := fun i hi => by
    obtain ⟨w, hwae, hwhol⟩ := hC (F i) (fun k => F (nxt i k)) (hFint i (by omega))
      (fun k => by
        rw [ofReal_two_mul_natCast]
        exact memLp_two_mul_of_gradClosed_fullStep hd c hdep hr hrR hgrad hmem (nxt i k)
          (by have := hdep i k; omega))
      ((hgrad i (by omega)).mono hsub)
    exact ⟨w, hwae, _, by rwa [morreyExponent_two_mul hd] at hwhol⟩
  choose! v hvae hvhol using hex
  obtain ⟨hfd, hcn⟩ := contDiffOn_of_ae_eq_family (F := F) (v := v) Metric.isOpen_ball
    (fun n i => dep i + n + 1 + d / 2 ≤ m) (fun n i k hi => by have := hdep i k; omega)
    (fun n i hi => hvae i (by omega)) (fun n i hi => hFint i (by omega))
    (fun n i hi => (hgrad i (by omega)).mono hsub)
    (fun n i hi => (hvhol i (by omega)).choose_spec.continuousOn (by norm_num))
  exact ⟨v, hvae, hvhol, hcn, fun i hi => hfd 0 i (by omega)⟩


/-! ### Hölder estimate with its constant -/

/-- **Guo's clause (ii) with its constant against the `L²` data.** Composing the ladder's
constant with Morrey's gives one constant, depending on the dimension, the rung count, the
exponent and the two radii, bounding the Hölder seminorm of every member by a uniform `L²` bound
on the family over the outer ball. This is the shape of Guo's
`‖u‖_{C^{k-1-⌊n/p⌋,γ}} ≤ C‖u‖_{W^{k,p}}` at `p = 2`. -/
theorem exists_const_holderOnWith_of_gradClosed_of_bound (hd : 0 < d)
    (c : EuclideanSpace ℝ (Fin d)) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (ι : Type*)
    {s : ℕ} {P : ℝ≥0} (hsd : 2 * s ≤ d) (hP2 : (2 : ℝ≥0) ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : 2⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn (Metric.ball c R) (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) 2 (volume.restrict (Metric.ball c R))) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) 2 (volume.restrict (Metric.ball c R)) ≤ M) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict (Metric.ball c r)] F i ∧
            HolderOnWith (C * M) (morreyExponent d (P : ℝ)) w (Metric.ball c r) := by
  obtain ⟨Cm, hCm⟩ := morrey_ball hd hPd c hr
  obtain ⟨K, hK⟩ := exists_const_eLpNorm_le_of_gradClosed_fullStep hd c ι s hsd hP2 hPs hr hrR
  refine ⟨Cm * d * K, fun {F nxt dep m} hdep hgrad hmem M hM i hi => ?_⟩
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  have hbd : ∀ k, eLpNorm (F (nxt i k)) (ENNReal.ofReal (P : ℝ)) (volume.restrict (Metric.ball c r))
      ≤ ((K * M : ℝ≥0) : ℝ≥0∞) := fun k => by
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
    exact hK hdep hgrad hmem M hM (nxt i k) (by have := hdep i k; omega)
  obtain ⟨w, hwae, hwhol⟩ := hCm (F i) (fun k => F (nxt i k))
    (((hmem i (by omega)).mono_measure (Measure.restrict_mono hsub le_rfl)).integrable
      (by norm_num))
    (fun k => by
      rw [ENNReal.ofReal_coe_nnreal]
      exact memLp_of_gradClosed_fullStep hd c hdep s hsd hP2 hPs hr hrR hgrad hmem (nxt i k)
        (by have := hdep i k; omega))
    ((hgrad i (by omega)).mono hsub)
  refine ⟨w, hwae, hwhol.mono_const ?_⟩
  calc _ ≤ Cm * (d * (K * M)) := mul_le_mul_right (sum_toNNReal_eLpNorm_le hbd) _
    _ = Cm * d * K * M := by ring

end EllipticPdes.Embedding
