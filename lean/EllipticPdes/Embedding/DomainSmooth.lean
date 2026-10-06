/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.DomainHolder
public import EllipticPdes.Embedding.SmoothOfGradClosed
public import EllipticPdes.Embedding.ClassicalDeriv

/-!
# Classical derivatives up to the boundary

`EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain` produces a bounded
Hölder representative of each member separately. `u ∈ C^{k-1-⌊n/p⌋,γ}(closure Ω)` says more: one
function, differentiable to order `k - 1 - ⌊n/p⌋` on `Ω`, whose derivatives are the members
themselves and whose top derivatives are `γ`-Hölder on `closure Ω`. This file supplies that.

The representatives are chosen once, before any of them is read, so a single family `v` serves
every index. Each `v i` is continuous on `closure Ω`, hence on `Ω`, and integrable there, and
it has the weak gradient `fun k => v (nxt i k)` because a weak gradient sees only the
almost-everywhere class.
`EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn` then makes the weak
gradient a classical one at every point of `Ω`, and an induction on the order remaining reads
`ContDiffOn` off the chain.

The estimate is the one the clause states: the constant is quantified before the family, and it
bounds the supremum and the Hölder seminorm of every member on `closure Ω` by a uniform
`L^{p₀}` bound.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.3 case
(ii); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary)

variable {d : ℕ}

/-- **Clause (ii) of the embedding with classical derivatives.** One family of representatives
serves every index: each is bounded and Hölder on `closure Ω` under the constant the clause
names, each of low enough depth is differentiable on `Ω` with the next members as its partial
derivatives,
and each is `n` times continuously differentiable on `Ω` whenever the supply leaves `n` orders
above it. -/
theorem exists_const_contDiffOn_holderOnWith_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (ι : Type*) {p₀ P : ℝ≥0} (hp₀ : 1 ≤ p₀) {s : ℕ}
    (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∃ v : ι → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ i, dep i + 1 + s ≤ m → v i =ᵐ[volume.restrict Ω] F i) ∧
        (∀ i, dep i + 1 + s ≤ m → ∀ y ∈ closure Ω, ‖v i y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
        (∀ i, dep i + 1 + s ≤ m →
          HolderOnWith (C * M) (morreyExponent d (P : ℝ)) (v i) (closure Ω)) ∧
        (∀ (n : ℕ) (i : ι), dep i + n + 1 + s ≤ m → ContDiffOn ℝ (n : ℕ) (v i) Ω) ∧
        (∀ i, dep i + 2 + s ≤ m → ∀ y ∈ Ω,
          HasFDerivAt (v i) (gradCLM (fun k => v (nxt i k)) y) y) := by
  obtain ⟨C, hC⟩ :=
    exists_const_holderOnWith_of_gradClosed_domain hd hΩopen hΩb hC1 ι hp₀ hsd hp₀P hPd hPs
  refine ⟨C, fun {F nxt dep m} hdep hgrad hmem M hM => ?_⟩
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  have hγpos : 0 < morreyExponent d (P : ℝ) := by
    rw [← NNReal.coe_pos, coe_morreyExponent hPd (by omega), sub_pos,
      div_lt_one (lt_of_le_of_lt (by positivity) hPd)]
    exact hPd
  -- The representatives, chosen once.
  choose! v hvae hvsup hvhol using fun i (hi : dep i + 1 + s ≤ m) => hC hdep hgrad hmem M hM i hi
  obtain ⟨hfd, hcn⟩ := contDiffOn_of_ae_eq_family (F := F) (v := v) hΩopen
    (fun n i => dep i + n + 1 + s ≤ m) (fun n i k hi => by have := hdep i k; omega)
    (fun n i hi => hvae i (by omega))
    (fun n i hi => (hmem i (by omega)).integrable (by exact_mod_cast hp₀))
    (fun n i hi => hgrad i (by omega))
    (fun n i hi => ((hvhol i (by omega)).continuousOn hγpos).mono subset_closure)
  exact ⟨v, hvae, hvsup, hvhol, hcn, fun i hi => hfd 0 i (by omega)⟩

end EllipticPdes.Embedding
