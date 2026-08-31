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

What remains of Theorem III.2.2 after this file is the support clause and the norm bound.

## Main declarations

* `EllipticPdes.Extension.exists_lt_radius_of_isCompact_subset_ball`: a compact subset of an open
  ball sits in a strictly smaller one.
* `EllipticPdes.Extension.exists_extension`: the class extends across the whole boundary.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem III.2.2
(p. 20), proof step 3 (p. 22); L. C. Evans, *Partial Differential Equations* (2nd ed.),
§5.4 Theorem 1 (p. 253).
-/

open MeasureTheory Metric Set

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
      HasWeakGradOn Set.univ U G ∧ ∀ y ∈ Ω, U y = u y := by
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
  refine ⟨fun y => ∑ i, Ui i y, fun k y => ∑ i, Gi i k y, ?_, ?_⟩
  · exact hasWeakGradOn_finsetSum Finset.univ (fun i _ => hint i) (fun i _ k => hgint i k)
      (fun i _ => hwgi i)
  · intro y hy
    calc (∑ i, Ui i y) = ∑ i, P.part i y * u y :=
          Finset.sum_congr rfl fun i _ => hag i y hy
      _ = (∑ i, P.part i y) * u y := (Finset.sum_mul _ _ _).symm
      _ = u y := by rw [P.part_sum y (subset_closure hy), one_mul]

end EllipticPdes.Extension
