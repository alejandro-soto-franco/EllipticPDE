/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.SobolevLadder

/-!
# Sobolev ladder for a compactly supported family

The ladder of `EllipticPdes.Embedding.memLp_of_gradClosed_general` runs on a ball and shrinks it at
every rung, because each rung multiplies by a cutoff. A compactly supported class needs no
cutoff, so the same induction runs on the whole space with no loss of domain, and the
conclusion is global.

Two facts replace the finite measure of the ball. A compactly supported `Lᵖ` class is
integrable, and its exponent lowers freely: both come from
`MeasureTheory.MemLp.mono_exponent_of_measure_support_ne_top` applied to the support.

This is the half of the classical order-`k` embedding that asks nothing of a boundary. The
general statement on a bounded domain with `C¹` boundary reduces to it through an extension
operator, which is where the boundary hypothesis is spent.

## Main declarations

* `EllipticPdes.Embedding.integrable_of_memLp_compactSupport`: a compactly supported `Lᵖ`
  class is integrable.
* `EllipticPdes.Embedding.memLp_sobolevConj_of_le_compactSupport`: one rung on the whole
  space, fed by data at an exponent at or above `p`.
* `EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport`: the ladder, on the whole space.
* `EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal`: the ladder at the
  exponent case (i) names, under the strict condition `p₀ s < d`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1 and §5.6.3 Thm 6.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-! ### Compact support in place of a finite measure -/

/-- **Free lowering of the exponent of a compactly supported class.** The support has finite
measure, so Hölder's inequality on it gives the smaller exponent, with no hypothesis on the
measure of the whole space. -/
theorem memLp_mono_exponent_compactSupport {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcs : HasCompactSupport f) {p q : ℝ≥0∞} (hf : MemLp f q volume) (hpq : p ≤ q) :
    MemLp f p volume :=
  hf.mono_exponent_of_measure_support_ne_top
    (s := tsupport f) (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
    hcs.isCompact.measure_lt_top.ne hpq

/-- **Integrability of a compactly supported `Lᵖ` class**, for any `p ≥ 1`. -/
theorem integrable_of_memLp_compactSupport {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcs : HasCompactSupport f) {p : ℝ≥0} (hp : 1 ≤ p) (hf : MemLp f p volume) :
    Integrable f volume := by
  rw [← memLp_one_iff_integrable]
  exact memLp_mono_exponent_compactSupport hcs hf (by exact_mod_cast hp)

/-! ### One rung -/

/-- **One rung on the whole space.** A compactly supported `v` whose weak gradient `g` is
compactly supported and lies in `L^q` for some `q ≥ p` lies in `Lᵖ'`, where
`1/p' = 1/p - 1/d`. The exponents drop from `q` to `p` on the support, and
`exists_eLpNorm_sobolevConj_le_compactSupport` runs the rung. -/
theorem memLp_sobolevConj_of_le_compactSupport (hd : 0 < d) {p q p' : ℝ≥0}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {v : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hvcs : HasCompactSupport v) (hgcs : ∀ k, HasCompactSupport (g k))
    (hv : MemLp v q volume) (hg : ∀ k, MemLp (g k) q volume)
    (hwg : HasWeakGradOn Set.univ v g) :
    MemLp v p' volume := by
  have hpqE : (p : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hpq
  have hvp : MemLp v p volume := memLp_mono_exponent_compactSupport hvcs hv hpqE
  have hgp : ∀ k, MemLp (g k) p volume :=
    fun k => memLp_mono_exponent_compactSupport (hgcs k) (hg k) hpqE
  obtain ⟨_K, hK⟩ := exists_eLpNorm_sobolevConj_le_compactSupport hd hp hpp'
  exact (hK v g hvcs (integrable_of_memLp_compactSupport hvcs hp hvp) hvp hgp hwg).1

/-! ### The ladder -/

/-- **Sobolev ladder on the whole space.** Let `F` assign a function to each index of `ι`,
let `nxt i k` name a weak `k`-derivative of `F i` on `Set.univ`, and let `dep` record how far
an index sits above the root. If every member of the family is compactly supported, every
index of depth at most `m` lies in `L^{p₀}`, and every index of depth below `m` has its weak
gradient in the family, then at rung `s` with `p₀ s ≤ d` every index of depth at most `m - s`
lies in `L^q`, for any `q ≥ p₀` whose reciprocal is at least `1/p₀ - s/d`.

The statement is the one of `memLp_of_gradClosed_general` with the ball replaced by the whole
space and the radii gone: no rung shrinks the domain. -/
theorem memLp_of_gradClosed_compactSupport (hd : 1 < d)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (hcs : ∀ i, HasCompactSupport (F i)) :
    ∀ (s : ℕ) {q : ℝ≥0}, (p₀ : ℝ) * s ≤ (d : ℝ) → p₀ ≤ q →
      (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ →
      (∀ i, dep i < m → HasWeakGradOn Set.univ (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ volume) →
      ∀ i, dep i + s ≤ m → MemLp (F i) q volume := by
  intro s q hsd hpq hqs hgrad hmem i hi
  have hd0 : 0 < d := by omega
  have hrung : ∀ {p q' p' : ℝ≥0}, 1 ≤ p → p ≤ q' → (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ →
      ∀ j, dep j < m → (∀ k, MemLp (F (nxt j k)) q' volume) → MemLp (F j) q' volume →
        MemLp (F j) p' volume :=
    fun hp hpq' hpp' j hj hk hF => memLp_sobolevConj_of_le_compactSupport hd0 hp hpq' hpp'
      (hcs j) (fun k => hcs (nxt j k)) hF hk (hgrad j hj)
  refine ladder_induction (d := d) (fun s q (_ : Unit) => ∀ i, dep i + s ≤ m → MemLp (F i) q volume)
    (fun _ => True) id hp₀ (fun _ _ => trivial) (fun _ _ i hi => hmem i (by omega)) ?_ ?_ s ()
    trivial (fun _ => hd) hsd hpq hqs i hi
  · intro s _ _ p Q q hp hpQ hpp' hQ i hi
    exact hrung hp hpQ hpp' i (by omega) (fun k => hQ _ (by have := hdep i k; omega))
      (hQ i (by omega))
  · intro s _ _ P q hpq hqP hP h0 i hi
    exact memLp_mono_exponent_compactSupport (hcs i)
      (hrung hp₀ le_rfl hP i (by omega) (fun k => h0 _ (by have := hdep i k; omega))
        (h0 i (by omega))) (by exact_mod_cast hqP)

/-! ### The exponent of case (i) -/

/-- **Whole-space bootstrap at the exponent case (i) names.** Under the strict step condition
`p₀ s < d`, which is the `k < n/p` of Evans §5.6.3 Theorem 6, the reciprocal `1/p₀ - s/d` is
positive and names a finite exponent, and the bootstrap lands on it with no loss of domain.

The cited statement takes a bounded `Ω` with `C¹` boundary and concludes on it, with a norm
estimate. The statement here asks nothing of a boundary, takes a family of compact support on
the whole space, and is qualitative. The passage from the one to the other goes through the
extension operator, `EllipticPdes.Extension.exists_extension_subset_bound`, and the statement
it reaches on a bounded `C¹` domain is
`EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain`. -/
theorem memLp_of_gradClosed_compactSupport_ideal (hd : 1 < d)
    {ι : Type*} {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
    {dep : ι → ℕ} {m : ℕ} {p₀ : ℝ≥0} (hp₀ : 1 ≤ p₀)
    (hdep : ∀ i k, dep (nxt i k) ≤ dep i + 1) (hcs : ∀ i, HasCompactSupport (F i))
    (s : ℕ) (hsd : (p₀ : ℝ) * s < (d : ℝ))
    (hgrad : ∀ i, dep i < m → HasWeakGradOn Set.univ (F i) (fun k => F (nxt i k)))
    (hmem : ∀ i, dep i ≤ m → MemLp (F i) p₀ volume) :
    ∀ i, dep i + s ≤ m →
      MemLp (F i) (Real.toNNReal ((p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹)⁻¹) volume := by
  obtain ⟨Q, hp₀Q, hQ⟩ := exists_rung_exponent hp₀ (by omega) hsd
  rw [← hQ, inv_inv, Real.toNNReal_coe]
  exact memLp_of_gradClosed_compactSupport hd hp₀ hdep hcs s hsd.le hp₀Q hQ.ge hgrad hmem

end EllipticPdes.Embedding
