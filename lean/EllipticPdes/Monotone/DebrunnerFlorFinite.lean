/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.Basic
public import EllipticPdes.Monotone.KKM

/-!
# Debrunner–Flor inequality on a polytope

Ferreira–Gomes–Üçer (`ferreira-2025-sol-mea-gam`) cite the Debrunner–Flor lemma in the proof of
Theorem 2.16 (p. 11). Its finite-dimensional step says that a monotone operator `A` on the convex
hull `C` of finitely many points has a point `u ∈ C` with `0 ≤ ⟨A v, v - u⟩` for every `v ∈ C`.
This file proves that step from the KKM lemma of `EllipticPdes.Monotone.KKM`, in two parts. An
averaging identity shows that some vertex of a convex combination `u` of points of `K` satisfies
`0 ≤ ⟨A v, v - u⟩`. The sets `{u | 0 ≤ ⟨A v, v - u⟩}` then cover every face of the polytope in the
KKM sense, and compactness of the polytope passes from finite subfamilies to all of them.

None of the cited sources states the finite-dimensional lemma.

## Main declarations

* `EllipticPdes.IsMonotoneOp.exists_le_pairing_sum_smul`: for a convex combination
  `u = ∑ i, w i • v i` of points of `K`, some `i` with `0 < w i` has `0 ≤ ⟨A (v i), v i - u⟩`.
* `EllipticPdes.exists_minty_convexHull_finset`: the Debrunner–Flor inequality on the convex hull
  of a nonempty finite set.
-/

@[expose] public section

namespace EllipticPdes

open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Averaging lemma.** Let `A` be monotone on `K`, let `v i` lie in `K` and let the weights `w i`
be non-negative with sum `1`. Then some vertex `v i` of positive weight satisfies
`0 ≤ ⟨A (v i), v i - u⟩` for the convex combination `u = ∑ i, w i • v i`. The proof expands
`∑ i, w i * ⟨A (v i), v i - u⟩` as `(1/2) ∑ i, ∑ j, w i * w j * ⟨A (v i) - A (v j), v i - v j⟩`.
Monotonicity makes the double sum non-negative. -/
theorem IsMonotoneOp.exists_le_pairing_sum_smul {K : Set X} {A : X → StrongDual ℝ X}
    (hA : IsMonotoneOp K A) {ι : Type*} [Fintype ι] (v : ι → X) (hv : ∀ i, v i ∈ K) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    ∃ i, 0 < w i ∧ 0 ≤ A (v i) (v i - ∑ j, w j • v j) := by
  set u : X := ∑ j, w j • v j with hu
  -- `v i - u = ∑ j, w j • (v i - v j)`.
  have hdiff : ∀ i, v i - u = ∑ j, w j • (v i - v j) := fun i => by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul, hu]
  set S : ℝ := ∑ i, ∑ j, w i * w j * A (v i) (v i - v j) with hS
  have hsum : ∑ i, w i * A (v i) (v i - u) = S := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdiff i, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, mul_assoc]
  have hswap : S = ∑ i, ∑ j, w i * w j * A (v j) (v j - v i) := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnonneg : 0 ≤ S := by
    have h2 : 2 * S = ∑ i, ∑ j, w i * w j * (A (v i) - A (v j)) (v i - v j) := by
      calc 2 * S = S + S := by ring
        _ = ∑ i, ∑ j, w i * w j * ((A (v i) - A (v j)) (v i - v j)) := by
          conv_lhs => arg 2; rw [hswap]
          rw [hS, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          have : v j - v i = -(v i - v j) := by abel
          simp only [sub_apply, this, map_neg]
          ring
    have : 0 ≤ ∑ i, ∑ j, w i * w j * (A (v i) - A (v j)) (v i - v j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) (hA _ (hv i) _ (hv j))
    linarith
  by_contra hcon
  push Not at hcon
  have hlt : ∑ i, w i * A (v i) (v i - u) < 0 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < w i := by
      by_contra h
      push Not at h
      have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    calc ∑ i, w i * A (v i) (v i - u) < ∑ _i : ι, (0 : ℝ) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ _, ?_⟩
          · rcases (hw0 i).eq_or_lt with h | h
            · simp [← h]
            · exact (mul_neg_of_pos_of_neg h (hcon i h)).le
          · exact mul_neg_of_pos_of_neg hi₀ (hcon i₀ hi₀)
      _ = 0 := by simp
  linarith

/-- **Debrunner–Flor inequality on a polytope.** A monotone operator `A` on the convex hull `C` of a
nonempty finite set has a point `u ∈ C` with `0 ≤ ⟨A v, v - u⟩` for every `v ∈ C`. This is the
finite-dimensional step in the proof of Ferreira–Gomes–Üçer, Theorem 2.16 (p. 11). -/
theorem exists_minty_convexHull_finset {S : Finset X} (hS : S.Nonempty) {A : X → StrongDual ℝ X}
    (hA : IsMonotoneOp (convexHull ℝ (↑S : Set X)) A) :
    ∃ u ∈ convexHull ℝ (↑S : Set X), ∀ v ∈ convexHull ℝ (↑S : Set X), 0 ≤ A v (v - u) := by
  set C : Set X := convexHull ℝ (↑S : Set X) with hCdef
  have hCc : IsCompact C := S.finite_toSet.isCompact_convexHull ℝ
  have hCconv : Convex ℝ C := convex_convexHull ℝ _
  let t : C → Set X := fun v => {u | 0 ≤ A v.1 (v.1 - u)}
  have htc : ∀ v, IsClosed (t v) := fun v =>
    isClosed_le continuous_const ((A v.1).continuous.comp (continuous_const.sub continuous_id))
  have hfin : ∀ F : Finset C, (C ∩ ⋂ v ∈ F, t v).Nonempty := by
    intro F
    rcases F.eq_empty_or_nonempty with rfl | hF
    · obtain ⟨s₀, hs₀⟩ := hS
      exact ⟨s₀, subset_convexHull ℝ _ hs₀, by simp⟩
    have : Nonempty F := hF.to_subtype
    let x : F → X := fun i => i.1.1
    have hx : ∀ i, x i ∈ C := fun i => i.1.2
    have hcov : ∀ s : Finset F, convexHull ℝ (x '' ↑s) ⊆ ⋃ i ∈ s, {u | 0 ≤ A (x i) (x i - u)} := by
      intro s p hp
      rw [mem_convexHull_iff_exists_fintype] at hp
      obtain ⟨ι, _, w, z, hw0, hw1, hz, hpz⟩ := hp
      have hzC : ∀ i, z i ∈ C := fun i => by
        obtain ⟨a, _, ha⟩ := hz i
        exact ha ▸ hx a
      obtain ⟨i, -, hi⟩ := hA.exists_le_pairing_sum_smul z hzC w hw0 hw1
      obtain ⟨a, ha, haz⟩ := hz i
      have hp' : p = ∑ j, w j • z j := by
        exact hpz.symm
      simp only [mem_iUnion]
      refine ⟨a, ha, ?_⟩
      change 0 ≤ A (x a) (x a - p)
      rw [hp']
      have : x a = z i := haz
      rw [this]
      exact hi
    obtain ⟨p, hp1, hp2⟩ := kkm x (fun i => {u | 0 ≤ A (x i) (x i - u)})
      (fun i => isClosed_le continuous_const
        ((A (x i)).continuous.comp (continuous_const.sub continuous_id))) hcov
    refine ⟨p, ?_, ?_⟩
    · exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hx i) hCconv hp1
    · simp only [mem_iInter]
      intro v hv
      exact mem_iInter.mp hp2 (⟨v, hv⟩ : F)
  obtain ⟨u, huC, hu⟩ := hCc.inter_iInter_nonempty t htc hfin
  exact ⟨u, huC, fun v hv => by simpa [t] using mem_iInter.mp hu ⟨v, hv⟩⟩

end EllipticPdes
