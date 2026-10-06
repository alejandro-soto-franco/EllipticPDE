/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.DomainSobolev
public import EllipticPdes.Embedding.SobolevLadder

/-!
# Sobolev ladder on a bounded domain

The proof of the Sobolev embedding at order `k` applies the Gagliardo-Nirenberg-Sobolev
inequality to
`D^β u` for `|β| ≤ k - 1`, reads off `u ∈ W^{k-1,p⋆}(Ω)`, and repeats. This file runs that
iteration.

`EllipticPdes.Embedding.memLp_of_gradClosed_general` runs the same iteration on a ball inside a
ball, each rung shrinking the domain because the whole-space inequality is fed through a cutoff.
On a bounded domain with `C¹` boundary the extension operator supplies the cutoff once and for
all, so no rung shrinks anything and the estimate is on `Ω` throughout. That is what makes a
constant possible: one number, depending on the domain, the dimension, the base exponent, the
rung count and the target exponent, takes a uniform `L^{p₀}` bound on the family to an `L^q`
bound on the member.

## Two regimes of a rung

The step onto the target `q` consumes the exponent `p` with `1/p = 1/q + 1/d`, which is
admissible when `1/q + 1/d ≤ 1`. Below that the target sits under the conjugate exponent and one
rung from `p₀` overshoots it; the exponent is then lowered onto the target by the finite measure
of the domain, at the price of a factor `|Ω|^{1/q - 1/P}` the constant absorbs. Both regimes are
what `EllipticPdes.Embedding.memLp_of_gradClosed_general` separates on a ball.

## Main declarations

* `EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`: the ladder on the domain,
  with a constant taken before the family.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.3 case
(i); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (i).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary)

variable {d : ℕ}

/-- **Sobolev ladder on a bounded domain with `C¹` boundary and its constant.** Let `F`
assign a class to each index of `ι`, let `nxt i k` name a weak `k`-derivative of `F i` on `Ω`,
and let `dep` record how far an index sits above the root, so that differentiating adds at most
one. At rung `s` with `p₀ s ≤ d`, one constant takes a uniform `L^{p₀}` bound on the members of
depth at most `m` to an `L^q` bound on every member of depth at most `m - s`, for any `q ≥ p₀`
whose reciprocal is at least `1/p₀ - s/d`. This is the embedding's case (i), read on a
family closed under weak differentiation with a depth function in place of `D^α u`. -/
theorem exists_const_memLp_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀) (ι : Type*) :
    ∀ (s : ℕ) {q : ℝ≥0}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ →
      ∃ K : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
        {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
        (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
        (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
        ∀ M : ℝ≥0∞, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ M) →
        ∀ i, dep i + s ≤ m →
          MemLp (F i) q (volume.restrict Ω) ∧
            eLpNorm (F i) q (volume.restrict Ω) ≤ (K : ℝ≥0∞) * M := by
  intro s q hsd hpq hqs
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  exact exists_const_ladder ι (fun _ : Unit => Ω) (fun _ => True) id Ω hp₀ (fun _ _ => trivial)
    (fun _ _ => subset_rfl) (fun _ _ => this)
    (fun _ _ p q p' hp hpq hpp' => exists_eLpNorm_sobolevConj_le_domain_of_le (by omega) hΩopen hΩb
      hC1 hp hpq hpp') s () trivial (fun _ => hd) hsd hpq hqs

end EllipticPdes.Embedding
