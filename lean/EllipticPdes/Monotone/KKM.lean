/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Brouwer.Brouwer
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Knaster–Kuratowski–Mazurkiewicz lemma

Closed sets `C i` indexed by the vertices of a simplex cover it in the KKM sense when every face is
covered by the sets of its own vertices. The lemma states that such a family has a common point.
This file derives it from Brouwer's fixed-point theorem
(`EllipticPdes.Brouwer.brouwer_fixed_point` of
`EllipticPdes.Brouwer.Brouwer`): a common-point-free family gives a continuous self-map of the
simplex whose fixed point contradicts the covering condition.

The lemma is the input to the Debrunner–Flor theorem and the Browder–Minty theorem. It is the
closed-set form of Knaster–Kuratowski–Mazurkiewicz (Fund. Math. 14, 1929). None of the cited
sources states it.

## Main declarations

* `EllipticPdes.kkm_stdSimplex`: the KKM lemma on the standard simplex `stdSimplex ℝ ι`.
* `EllipticPdes.kkm`: the KKM lemma on the convex hull of finitely many points of a real normed
  space.
-/

@[expose] public section

-- Mathlib deprecated the set `stdSimplex` in favour of the type `Convexity.StdSimplex`. This file
-- states the lemma for the explicit set and uses `stdSimplex` only to reach its topology.
set_option linter.deprecated false

namespace EllipticPdes

open Set

/-- **KKM lemma on the standard simplex.** If closed sets `C i` cover every face of `stdSimplex ℝ ι`
by the sets of its own vertices, then they have a common point in the simplex. The simplex is the
set `stdSimplex ℝ ι` of non-negative vectors with coordinate sum `1`. The index type is nonempty,
since the simplex is empty otherwise. -/
theorem kkm_stdSimplex {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Set (ι → ℝ)) (hC : ∀ i, IsClosed (C i))
    (hcov : ∀ s : Finset ι, ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) → ∑ i, x i = 1 → (∀ i ∉ s, x i = 0) →
      ∃ i ∈ s, x ∈ C i) :
    ({x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} ∩ ⋂ i, C i).Nonempty := by
  classical
  change (stdSimplex ℝ ι ∩ ⋂ i, C i).Nonempty
  by_contra hempty
  have hne : ∀ i, (C i).Nonempty := fun i =>
    let ⟨j, hj, hjC⟩ := hcov {i} (Pi.single i 1) (single_mem_stdSimplex ℝ i).1
      (single_mem_stdSimplex ℝ i).2
      (fun j hj => by simp_all)
    ⟨_, (Finset.mem_singleton.mp hj) ▸ hjC⟩
  set d : ι → (ι → ℝ) → ℝ := fun i x => Metric.infDist x (C i) with hd
  have hdc : ∀ i, Continuous (d i) := fun i => Metric.continuous_infDist_pt _
  have hd0 : ∀ i x, 0 ≤ d i x := fun i x => Metric.infDist_nonneg
  have hdpos : ∀ i x, 0 < d i x ↔ x ∉ C i := fun i x => by
    rw [(hC i).notMem_iff_infDist_pos (hne i)]
  have hS : ∀ x ∈ stdSimplex ℝ ι, 0 < ∑ j, d j x := fun x hx => by
    by_contra hS
    refine hempty ⟨x, hx, mem_iInter.mpr fun i => ?_⟩
    by_contra hi
    have h1 := (hdpos i x).mpr hi
    have h2 := Finset.single_le_sum (f := fun j => d j x) (fun j _ => hd0 j x) (Finset.mem_univ i)
    exact hS (lt_of_lt_of_le h1 h2)
  let F : stdSimplex ℝ ι → stdSimplex ℝ ι := fun x =>
    ⟨fun i => d i x / ∑ j, d j x, fun i =>
      div_nonneg (hd0 _ _) (Finset.sum_nonneg fun j _ => hd0 _ _),
      by
        change ∑ i, d i x / ∑ j, d j x = 1
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ (hS x x.2).ne'⟩
  have hFc : Continuous F := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
    refine Continuous.div ((hdc i).comp continuous_subtype_val)
      (continuous_finsetSum _ fun j _ => (hdc j).comp continuous_subtype_val)
      fun x => (hS x x.2).ne'
  obtain ⟨x, hx⟩ := Brouwer.brouwer_fixed_point (stdSimplex ℝ ι) (convex_stdSimplex ℝ ι)
    (isCompact_stdSimplex ℝ ι) (⟨Pi.single (Classical.arbitrary ι) 1,
      single_mem_stdSimplex ℝ _⟩) ⟨F, hFc⟩
  have hxi : ∀ i, (x : ι → ℝ) i = d i x / ∑ j, d j x := fun i => by
    have := congrArg (fun y : stdSimplex ℝ ι => (y : ι → ℝ) i) hx
    exact this.symm
  have hpos : ∀ i, 0 < (x : ι → ℝ) i ↔ (x : ι → ℝ) ∉ C i := fun i => by
    rw [hxi i, ← hdpos]
    exact div_pos_iff_of_pos_right (hS x x.2)
  obtain ⟨i, hi, hiC⟩ := hcov (Finset.univ.filter fun i => 0 < (x : ι → ℝ) i) x x.2.1 x.2.2
    (fun i hi => le_antisymm (not_lt.mp (by simpa using hi)) (x.2.1 i))
  exact (hpos i).mp (by simpa using hi) hiC

/-- A convex combination of the points `x i`, supported on `s`, lies in the convex hull of the
points indexed by `s`. -/
private lemma sum_smul_mem_convexHull {X : Type*} [AddCommGroup X] [Module ℝ X] {ι : Type*}
    [Fintype ι] (x : ι → X) (s : Finset ι) {l : ι → ℝ} (hl0 : ∀ i, 0 ≤ l i)
    (hl1 : ∑ i, l i = 1) (hs : ∀ i ∉ s, l i = 0) :
    ∑ i, l i • x i ∈ convexHull ℝ (x '' (s : Set ι)) := by
  classical
  have h1 : ∑ i, l i • x i = ∑ i ∈ s, l i • x i :=
    (Finset.sum_subset s.subset_univ fun i _ hi => by simp [hs i hi]).symm
  have h2 : ∑ i ∈ s, l i = 1 := by
    rw [← hl1]
    exact Finset.sum_subset s.subset_univ fun i _ hi => hs i hi
  rw [h1]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => hl0 i) h2
    fun i hi => subset_convexHull ℝ _ (mem_image_of_mem x hi)

/-- **KKM lemma.** If closed sets `C i` cover the convex hull of every sub-family of finitely many
points `x i` of a real normed space by the sets of that sub-family, then the sets have a common
point in the convex hull of all the points. -/
theorem kkm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type*} [Finite ι]
    [Nonempty ι] (x : ι → X) (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hcov : ∀ s : Finset ι, convexHull ℝ (x '' s) ⊆ ⋃ i ∈ s, C i) :
    (convexHull ℝ (Set.range x) ∩ ⋂ i, C i).Nonempty := by
  classical
  have := Fintype.ofFinite ι
  let φ : (ι → ℝ) → X := fun l => ∑ i, l i • x i
  have hφ : Continuous φ := continuous_finsetSum _ fun i _ =>
    (continuous_apply i).smul continuous_const
  obtain ⟨l, ⟨hl0, hl1⟩, hlC⟩ := kkm_stdSimplex (fun i => φ ⁻¹' C i) (fun i => (hC i).preimage hφ)
    (fun s l hl0 hl1 hs => by
      simpa using hcov s (sum_smul_mem_convexHull x s hl0 hl1 hs))
  refine ⟨φ l, ?_, mem_iInter.mpr fun i => mem_iInter.mp hlC i⟩
  have := sum_smul_mem_convexHull x Finset.univ hl0 hl1 (fun i hi => absurd (Finset.mem_univ i) hi)
  simpa using this

end EllipticPdes
