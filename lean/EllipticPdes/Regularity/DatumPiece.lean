/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.ExtendCutoff
public import EllipticPdes.Regularity.L2Pairing
public import EllipticPdes.Regularity.IteratedSum

/-!
# One piece of the differentiated datum

Every term of the datum of Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2
step 3 has the same shape: a cutoff, a `W^{k,∞}` coefficient, and a derivative of the solution
of order at most two. The cutoff is the middle cutoff of the tower or one of its first two
partial derivatives, and it is what confines the term to the collar and lets it be extended by
zero to the whole domain.

This file turns that shape into a single lemma. Given the cutoff and the coefficient, there is a
constant such that every derivative with `k` weak derivatives on the collar produces a class on
the domain that has `k` weak derivatives, is bounded by the constant times the bound on the
derivative, and pairs against a test function as the product of the three factors.

The three conclusions are produced together because they are produced by the same construction:
`exists_iteratedWeakDeriv_mul` puts the coefficient in, `exists_iteratedWeakDeriv_extend_mulTest`
puts the cutoff in and moves the result to the domain, and the pairing is read off the
almost-everywhere description both of them are stated against.

## Main declarations

* `exists_datum_piece`: the class, its family, its bound, and its pairing.
* `exists_datum_of_pieces`: a finite family of pieces, assembled.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- **One piece of the datum.** For a cutoff `χ` supported in the collar `N ⊆ Ω` and a `W^{k,∞}`
coefficient `a`, there is a constant `K` such that every `p` with `k` weak derivatives on `N`
bounded by `M` yields a class `q` on `Ω` with

* `k` weak derivatives on `Ω`, bounded by `K·M`;
* `∫_Ω q·v = ∫_N χ·a·p·v` for every `v`.

The constant depends on the cutoff, the coefficient and the order alone, which is what keeps
the estimate of the induction step quantified before the solution and the datum. -/
theorem exists_datum_piece {Ω N : Set (EuclideanSpace ℝ (Fin d))}
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) (k : ℕ)
    {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsTestFn N χ)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : IsWkInfty a k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : L2D N} (hp : HasIteratedWeakDerivOn N k p) {M : ℝ},
      IteratedL2Bound hp M →
      ∃ (q : L2D Ω) (H : HasIteratedWeakDerivOn Ω k q),
        IteratedL2Bound H (K * M) ∧
        ∀ v : EuclideanSpace ℝ (Fin d) → ℝ,
          (∫ x in Ω, (q x : ℝ) * v x) = ∫ x in N, χ x * (a x * (p x : ℝ)) * v x := by
  obtain ⟨K1, hK1, hP1⟩ := exists_iteratedWeakDeriv_mul k ha
  obtain ⟨K2, hK2, hP2⟩ := exists_iteratedWeakDeriv_extend_mulTest hNm hNΩ k hχ
  refine ⟨K2 * K1, mul_nonneg hK2 hK1, ?_⟩
  intro p hp M hM
  -- The coefficient, then the cutoff.
  set ap : L2D N := mulL2 ha.measurable_self ha.ae_abs_le p with hap
  obtain ⟨Hap, hApbd⟩ :=
    hP1 hp (mulL2_coeFn ha.measurable_self ha.ae_abs_le p) hM
  have hmt : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), x ∈ N →
      ((mulTest hχ ap) x : ℝ)
        = χ x * (ap x : ℝ) :=
    (ae_restrict_iff' hNm).mp (mulCutoff_coeFn hχ ap)
  have hqae : (restrictL2 (Ω := Ω)
        (extendL2 hNm (mulTest hχ ap))
        : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        χ x * (extendL2 hNm ap x : ℝ) := by
    filter_upwards [coeFn_restrictL2 (Ω := Ω)
        (extendL2 hNm (mulTest hχ ap)),
      ae_restrict_of_ae (coeFn_extendL2 hNm
        (mulTest hχ ap)),
      ae_restrict_of_ae (coeFn_extendL2 hNm ap),
      ae_restrict_of_ae hmt] with x h1 h2 h3 h4
    rw [h1, h2, h3]
    by_cases hxN : x ∈ N
    · rw [Set.indicator_of_mem hxN, Set.indicator_of_mem hxN, h4 hxN]
    · rw [Set.indicator_of_notMem hxN, Set.indicator_of_notMem hxN, mul_zero]
  obtain ⟨H, hHbd⟩ := hP2 Hap hqae hApbd
  refine ⟨_, H, by rw [mul_assoc]; exact hHbd, fun v => ?_⟩
  -- The pairing, read off the same description.
  have e1 : (∫ x in Ω, (restrictL2 (Ω := Ω)
        (extendL2 hNm (mulTest hχ ap)) x : ℝ) * v x)
      = ∫ x in Ω, χ x
          * (extendL2 hNm ap x : ℝ) * v x := by
    refine integral_congr_ae ?_
    filter_upwards [hqae] with x hx
    rw [hx]
  have e2 : (∫ x in Ω, χ x
        * (extendL2 hNm ap x : ℝ) * v x)
      = ∫ x, χ x * (extendL2 hNm ap x : ℝ) * v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [show χ x = 0 from image_eq_zero_of_notMem_tsupport
        (fun hc => hx (hNΩ (hχ.2.2 hc)))]
      ring)
  rw [e1, e2, integral_extendL2_mul_mul hNm _ χ v]
  refine integral_congr_ae ?_
  filter_upwards [mulL2_coeFn ha.measurable_self ha.ae_abs_le p] with x hx
  rw [hx]

/-- **Pairing of a datum with `k` weak derivatives.** The functional `T` on test functions is
the pairing against an `L²(Ω)` class that has `k` weak derivatives with `L²` norms at most `B`.
Pairings of this kind are closed under signed sums, which is how the datum of an induction step
is assembled from its pieces. -/
def IsDatumPairing (Ω : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (B : ℝ)
    (T : (EuclideanSpace ℝ (Fin d) → ℝ) → ℝ) : Prop :=
  ∃ (F : L2D Ω) (HF : HasIteratedWeakDerivOn Ω k F), IteratedL2Bound HF B ∧
    ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      (∫ x in Ω, (F x : ℝ) * v x) = T v

namespace IsDatumPairing

variable {Ω : Set (EuclideanSpace ℝ (Fin d))} {k : ℕ} {B B' : ℝ}
  {T T' : (EuclideanSpace ℝ (Fin d) → ℝ) → ℝ}

/-- A pairing with a larger bound. -/
theorem mono (h : IsDatumPairing Ω k B T) (hB : B ≤ B') : IsDatumPairing Ω k B' T := by
  obtain ⟨F, HF, hFB, hF⟩ := h
  exact ⟨F, HF, hFB.mono_const hB, hF⟩

/-- Pairings that agree on test functions are interchangeable. -/
theorem congr (h : IsDatumPairing Ω k B T)
    (hT : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v → HasCompactSupport v →
      T v = T' v) : IsDatumPairing Ω k B T' := by
  obtain ⟨F, HF, hFB, hF⟩ := h
  exact ⟨F, HF, hFB, fun v hvc hvcs => (hF v hvc hvcs).trans (hT v hvc hvcs)⟩

/-- The pairings add, with the bounds. -/
theorem add (h : IsDatumPairing Ω k B T) (h' : IsDatumPairing Ω k B' T') :
    IsDatumPairing Ω k (B + B') fun v => T v + T' v := by
  obtain ⟨F, HF, hFB, hF⟩ := h
  obtain ⟨F', HF', hFB', hF'⟩ := h'
  exact ⟨F + F', HF.add HF', hFB.add hFB', fun v hvc hvcs => by
    rw [setIntegral_add_mul_testFn _ _ hvc hvcs, hF v hvc hvcs, hF' v hvc hvcs]⟩

/-- The pairings subtract, with the bounds adding. -/
theorem sub (h : IsDatumPairing Ω k B T) (h' : IsDatumPairing Ω k B' T') :
    IsDatumPairing Ω k (B + B') fun v => T v - T' v := by
  obtain ⟨F, HF, hFB, hF⟩ := h
  obtain ⟨F', HF', hFB', hF'⟩ := h'
  exact ⟨F - F', HF.sub HF', hFB.sub hFB', fun v hvc hvcs => by
    rw [setIntegral_sub_mul_testFn _ _ hvc hvcs, hF v hvc hvcs, hF' v hvc hvcs]⟩

end IsDatumPairing

/-- **Finite family of pieces assembled.** The datum of the induction step is a fixed finite
list of shapes, each a cutoff against a coefficient against a derivative, and only the
derivatives depend on the solution. Quantifying the constant before the derivatives is what
makes that work: the cutoffs and coefficients are data of the operator and the tower, so
their constants are summed once.

The pairing is asked of a test function rather than of an arbitrary weight, since splitting the
integral of the sum into the sum of the integrals is where integrability enters. -/
theorem exists_datum_of_pieces {Ω N : Set (EuclideanSpace ℝ (Fin d))}
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) (k : ℕ) {ι : Type*} [Fintype ι]
    {χ : ι → EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ∀ t, IsTestFn N (χ t))
    {a : ι → EuclideanSpace ℝ (Fin d) → ℝ} (ha : ∀ t, IsWkInfty (a t) k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ι → L2D N) (hp : ∀ t, HasIteratedWeakDerivOn N k (p t)) {M : ℝ},
      (∀ t, IteratedL2Bound (hp t) M) →
      IsDatumPairing Ω k (K * M) fun v => ∑ t, ∫ x in N, χ t x * (a t x * (p t x : ℝ)) * v x := by
  classical
  choose K hK hP using fun t => exists_datum_piece hNm hNΩ k (hχ t) (ha t)
  refine ⟨∑ t, K t, Finset.sum_nonneg fun t _ => hK t, ?_⟩
  intro p hp M hM
  choose q Hq hqbd hqpair using fun t => hP t (hp t) (hM t)
  refine ⟨∑ t, q t, HasIteratedWeakDerivOn.sum Hq, ?_, fun v hvc hvcs => ?_⟩
  · have hsum := IteratedL2Bound.sum (H := Hq) (C := fun t => K t * M) hqbd
    rwa [← Finset.sum_mul] at hsum
  · rw [setIntegral_sum_mul_testFn q hvc hvcs]
    exact Finset.sum_congr rfl fun t _ => hqpair t v

/-- **Pieces whose coefficients depend on a direction.** The constant of
`exists_datum_of_pieces` for a family of coefficients indexed by a finite set of directions can
be taken to serve every direction at once, which is what lets the constant of the induction step
be quantified before the direction of differentiation. The bound `M` is nonnegative so that
enlarging the constant enlarges the bound. -/
theorem exists_datum_of_pieces_dir {Ω N : Set (EuclideanSpace ℝ (Fin d))}
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) (k : ℕ) {σ ι : Type*} [Finite σ] [Fintype ι]
    {χ : ι → EuclideanSpace ℝ (Fin d) → ℝ} (hχ : ∀ t, IsTestFn N (χ t))
    {a : σ → ι → EuclideanSpace ℝ (Fin d) → ℝ} (ha : ∀ m t, IsWkInfty (a m t) k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : σ) (p : ι → L2D N)
      (hp : ∀ t, HasIteratedWeakDerivOn N k (p t)) {M : ℝ}, 0 ≤ M →
      (∀ t, IteratedL2Bound (hp t) M) →
      IsDatumPairing Ω k (K * M) fun v =>
        ∑ t, ∫ x in N, χ t x * (a m t x * (p t x : ℝ)) * v x := by
  have := Fintype.ofFinite σ
  choose K hK hP using fun m => exists_datum_of_pieces hNm hNΩ k hχ (ha m)
  refine ⟨∑ m, K m, Finset.sum_nonneg fun m _ => hK m, fun m p hp M hM0 hM => ?_⟩
  exact (hP m p hp hM).mono (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun m _ => hK m) (Finset.mem_univ m)) hM0)

end EllipticPdes.Regularity
