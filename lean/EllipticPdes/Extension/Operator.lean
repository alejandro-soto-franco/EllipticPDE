/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Extension.LocalExtension

/-!
# Gluing the local extensions

Guo's third step covers the boundary, fixes a partition of unity subordinate to that cover with
each support compactly inside its neighbourhood, and sets `ū = ∑ᵢ Pᵢ ūᵢ`. This file carries out
that sum.

Each piece is a local extension cut down by its piece of the partition, so the cutoff comes
after the extension. That order is what makes the sum agree with the class: where a piece of the
partition is nonzero the point lies in that chart's ball, where the local extension agrees with
the class, so the piece equals `Pᵢ u` there and off the ball both sides vanish. The pieces then
add to `u` because the partition adds to one.

`supp(Pᵢ) ⋐ Wᵢ` is compact containment, and the local extension of step 2 lives on a ball
strictly inside the chart's, so the support is first pushed into a smaller ball. A compact subset
of an open ball admits one.

The support clause follows by one more cutoff, which is how Guo reaches it: any open set the
closure of the domain sits in admits a smooth cutoff equal to one on that closure, and
multiplying by it moves the support inside without disturbing the agreement. What remains of Theorem III.2.2
after this file is the norm bound.

## Main declarations

* `EllipticPdes.Extension.exists_lt_radius_of_isCompact_subset_ball`: a compact subset of an open
  ball sits in a strictly smaller one.
* `EllipticPdes.Extension.exists_extension`: the class extends across the whole boundary.
* `EllipticPdes.Extension.exists_cutoff_one_on_compact`: a smooth cutoff between a compact set
  and an open one.
* `EllipticPdes.Extension.exists_extension_subset`: clauses (i) and (ii) of the theorem.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 22); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

open MeasureTheory Metric Set
open scoped Manifold

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding
  (HasWeakGradOn hasWeakGradOn_univ_mul_cutoff hasWeakGradOn_finsetSum integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- **Shrinking an open ball around a compact subset.** -/
theorem exists_lt_radius_of_isCompact_subset_ball {K : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} {R : ℝ} (hR : 0 < R) (hK : IsCompact K)
    (hKR : K ⊆ ball x R) : ∃ r, r < R ∧ 0 < r ∧ K ⊆ ball x r := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨R / 2, by linarith, by linarith, by simp⟩
  · obtain ⟨y, hyK, hy⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
    have hyR : dist y x < R := mem_ball.mp (hKR hyK)
    refine ⟨(dist y x + R) / 2, by linarith, by
      have : 0 ≤ dist y x := dist_nonneg
      linarith, fun z hz => ?_⟩
    have hle : dist z x ≤ dist y x := hy hz
    exact mem_ball.mpr (by linarith)

private theorem intMul {B : Set (EuclideanSpace ℝ (Fin d))}
    {w h : EuclideanSpace ℝ (Fin d) → ℝ} (hw : IntegrableOn w B volume) (hcs : HasCompactSupport h)
    (hc : Continuous h) : IntegrableOn (fun x => h x * w x) B volume := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  exact (integrableOn_mul_bounded hw hc hC).congr
    (Filter.Eventually.of_forall fun x => mul_comm (w x) (h x))

/-- **Guo's third step** (Theorem III.2.2, proof step 3, p. 22): the local extensions glued with
the partition of unity extend the class across the whole boundary. -/
theorem exists_extension (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ Integrable U volume ∧
        (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  classical
  obtain ⟨P⟩ := nonempty_boundaryPartition hd hΩopen hΩb hC1
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hpiece : ∀ i : Option {x // x ∈ P.centres},
      ∃ (Ui : EuclideanSpace ℝ (Fin d) → ℝ) (Gi : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
        HasWeakGradOn Set.univ Ui Gi ∧ IntegrableOn Ui Set.univ volume ∧
          (∀ k, IntegrableOn (Gi k) Set.univ volume) ∧
          (∀ y ∈ Ω, Ui y = P.part i y * u y) := by
    rintro (_ | x)
    · have hcs : HasCompactSupport (P.part none) :=
        (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset
          (isClosed_tsupport _) (P.part_interior.trans hRb)
      have hpc : Continuous (P.part none) := (P.part_contDiff none).continuous
      have hpd : ∀ k : Fin d, Continuous (partialD k (P.part none)) := fun k =>
        ((P.part_contDiff none).continuous_fderiv (by simp)).clm_apply continuous_const
      have hpdcs : ∀ k : Fin d, HasCompactSupport (partialD k (P.part none)) := fun k =>
        hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
      have hiu : IntegrableOn (Ω.indicator u) Set.univ volume :=
        (hu.integrable_indicator hΩopen.measurableSet).integrableOn
      have hig : ∀ k, IntegrableOn (Ω.indicator (g k)) Set.univ volume := fun k =>
        ((hgi k).integrable_indicator hΩopen.measurableSet).integrableOn
      refine ⟨fun y => P.part none y * Ω.indicator u y,
        fun k y => P.part none y * Ω.indicator (g k) y
          + partialD k (P.part none) y * Ω.indicator u y,
        hasWeakGradOn_univ_mul_cutoff hΩopen.measurableSet (P.part_contDiff none) hcs
          P.part_interior hu hgi hwg,
        intMul hiu hcs hpc,
        fun k => (intMul (hig k) hcs hpc).add (intMul hiu (hpdcs k) (hpd k)), ?_⟩
      intro y hy
      dsimp only
      rw [Set.indicator_of_mem hy]
    · have hcs : HasCompactSupport (P.part (some x)) :=
        (isCompact_closedBall (x : EuclideanSpace ℝ (Fin d)) (P.chart x).radius).of_isClosed_subset
          (isClosed_tsupport _) ((P.part_boundary x).trans ball_subset_closedBall)
      obtain ⟨r, hrlt, hrpos, hrsub⟩ := exists_lt_radius_of_isCompact_subset_ball
        (P.chart x).radius_pos hcs (P.part_boundary x)
      obtain ⟨Ux, Gx, hUxwg, hUxint, hGxint, hUxag⟩ :=
        exists_localExtension (P.chart x) (P.chart_fits x x.2) hrlt hu hgi hwg
      have hpc : Continuous (P.part (some x)) := (P.part_contDiff (some x)).continuous
      have hpd : ∀ k : Fin d, Continuous (partialD k (P.part (some x))) := fun k =>
        ((P.part_contDiff (some x)).continuous_fderiv (by simp)).clm_apply continuous_const
      have hpdcs : ∀ k : Fin d, HasCompactSupport (partialD k (P.part (some x))) := fun k =>
        hcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
      have hiu : IntegrableOn ((ball (x : EuclideanSpace ℝ (Fin d)) r).indicator Ux)
          Set.univ volume :=
        (hUxint.integrableOn.integrable_indicator measurableSet_ball).integrableOn
      have hig : ∀ k, IntegrableOn
          ((ball (x : EuclideanSpace ℝ (Fin d)) r).indicator (Gx k)) Set.univ volume := fun k =>
        ((hGxint k).integrableOn.integrable_indicator measurableSet_ball).integrableOn
      refine ⟨fun y => P.part (some x) y * (ball (x : EuclideanSpace ℝ (Fin d)) r).indicator Ux y,
        fun k y => P.part (some x) y * (ball (x : EuclideanSpace ℝ (Fin d)) r).indicator (Gx k) y
          + partialD k (P.part (some x)) y
            * (ball (x : EuclideanSpace ℝ (Fin d)) r).indicator Ux y,
        hasWeakGradOn_univ_mul_cutoff measurableSet_ball (P.part_contDiff (some x)) hcs
          hrsub hUxint.integrableOn (fun k => (hGxint k).integrableOn) hUxwg,
        intMul hiu hcs hpc,
        fun k => (intMul (hig k) hcs hpc).add (intMul hiu (hpdcs k) (hpd k)), ?_⟩
      intro y hy
      dsimp only
      by_cases hyb : y ∈ ball (x : EuclideanSpace ℝ (Fin d)) r
      · rw [Set.indicator_of_mem hyb, hUxag y ⟨hy, hyb⟩]
      · rw [Set.indicator_of_notMem hyb,
          image_eq_zero_of_notMem_tsupport (fun hc => hyb (hrsub hc)), zero_mul, zero_mul]
  choose Ui Gi hwgi hint hgint hag using hpiece
  refine ⟨fun y => ∑ i, Ui i y, fun k y => ∑ i, Gi i k y, ?_, ?_, ?_, ?_⟩
  · exact hasWeakGradOn_finsetSum Finset.univ (fun i _ => hint i) (fun i _ k => hgint i k)
      (fun i _ => hwgi i)
  · exact MeasureTheory.integrable_finsetSum _ fun i _ => integrableOn_univ.mp (hint i)
  · exact fun k => MeasureTheory.integrable_finsetSum _ fun i _ =>
      integrableOn_univ.mp (hgint i k)
  · intro y hy
    calc (∑ i, Ui i y) = ∑ i, P.part i y * u y :=
          Finset.sum_congr rfl fun i _ => hag i y hy
      _ = (∑ i, P.part i y) * u y := (Finset.sum_mul _ _ _).symm
      _ = u y := by rw [P.part_sum y (subset_closure hy), one_mul]

/-- **Cutting between a compact set and an open one.** A smooth cutoff equal to one on the
compact set and compactly supported inside the open one. -/
theorem exists_cutoff_one_on_compact {K U : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ y ∈ K, χ y = 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf0, hf1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
      (isOpen_interior (s := L)).isClosed_compl hK.isClosed
      (by
        rw [Set.disjoint_compl_left_iff_subset]
        exact hKL)
  have hsupp : tsupport (fun y => f y) ⊆ L := by
    refine closure_minimal ?_ hLc.isClosed
    intro y hy
    by_contra hc
    exact hy (hf0 fun hcc => hc (interior_subset hcc))
  exact ⟨fun y => f y, contMDiff_iff_contDiff.mp f.contMDiff,
    hLc.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hLU,
    fun y hy => hf1 hy⟩

/-- **Guo's Theorem III.2.2, clauses (i) and (ii)** (p. 20). The extension agrees with the class
on the domain and is supported inside any open set the closure of the domain sits in. -/
theorem exists_extension_subset (hd : 0 < d) {Ω Ω' : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω)
    (hΩ'open : IsOpen Ω') (hsub : closure Ω ⊆ Ω')
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u Ω volume) (hgi : ∀ k, IntegrableOn (g k) Ω volume)
    (hwg : HasWeakGradOn Ω u g) :
    ∃ (U : EuclideanSpace ℝ (Fin d) → ℝ) (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasWeakGradOn Set.univ U G ∧ HasCompactSupport U ∧ tsupport U ⊆ Ω' ∧
        Integrable U volume ∧ (∀ k, Integrable (G k) volume) ∧ ∀ y ∈ Ω, U y = u y := by
  obtain ⟨U0, G0, hwg0, hint0, hgint0, hag0⟩ :=
    exists_extension hd hΩopen hΩb hC1 hu hgi hwg
  obtain ⟨Rb, hRb⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hclc : IsCompact (closure Ω) :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) Rb).of_isClosed_subset isClosed_closure
      (closure_minimal hRb (isClosed_closedBall))
  obtain ⟨χ, hχc, hχcs, hχs, hχ1⟩ := exists_cutoff_one_on_compact hclc hΩ'open hsub
  have hmul := hasWeakGradOn_univ_mul_cutoff (B := Set.univ) MeasurableSet.univ hχc hχcs
    (Set.subset_univ _) hint0.integrableOn (fun k => (hgint0 k).integrableOn) hwg0
  simp only [Set.indicator_univ] at hmul
  obtain ⟨Cχ, hCχ⟩ := hχcs.exists_bound_of_continuous hχc.continuous
  have hχpc : ∀ k : Fin d, Continuous (partialD k χ) := fun k =>
    (hχc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχpcs : ∀ k : Fin d, HasCompactSupport (partialD k χ) := fun k =>
    hχcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hprod : ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ) (h : EuclideanSpace ℝ (Fin d) → ℝ),
      Integrable w volume → HasCompactSupport h → Continuous h →
      Integrable (fun y => h y * w y) volume := by
    intro w h hw hcs hc
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
    exact integrableOn_univ.mp ((integrableOn_mul_bounded hw.integrableOn hc hC).congr
      (Filter.Eventually.of_forall fun y => mul_comm (w y) (h y)))
  have hsuppU : tsupport (fun y => χ y * U0 y) ⊆ Ω' := by
    refine subset_trans (closure_mono ?_) hχs
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc, zero_mul])
  refine ⟨fun y => χ y * U0 y, fun k y => χ y * G0 k y + partialD k χ y * U0 y, hmul,
    hχcs.of_isClosed_subset (isClosed_tsupport _) ?_, hsuppU,
    hprod _ _ hint0 hχcs hχc.continuous,
    fun k => (hprod _ _ (hgint0 k) hχcs hχc.continuous).add
      (hprod _ _ hint0 (hχpcs k) (hχpc k)), ?_⟩
  · refine subset_trans (closure_mono ?_) subset_rfl
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hc
    exact hy (by rw [hc, zero_mul])
  · intro y hy
    dsimp only
    rw [hχ1 y (subset_closure hy), one_mul, hag0 y hy]

end EllipticPdes.Extension
