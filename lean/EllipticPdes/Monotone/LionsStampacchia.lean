/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.DebrunnerFlor

/-!
# Minty's lemma and the Lions–Stampacchia theorem

For a monotone operator `A : X → X*` on a convex set `K`, the weak inequality
`0 ≤ ⟨A v, v - u⟩` for all `v ∈ K` and the strong inequality `0 ≤ ⟨A u, v - u⟩` for all `v ∈ K`
are equivalent when `A` is hemicontinuous (Ferreira–Gomes–Üçer, `ferreira-2025-sol-mea-gam`,
Remark 2.17, p. 12). The strong direction needs hemicontinuity and the weak direction needs
monotonicity. Subtracting a datum `f ∈ X*` from `A` keeps monotonicity, hemicontinuity and
coercivity, so the weak variational inequality of `EllipticPdes.exists_weakVI` yields the
Lions–Stampacchia theorem: a solution `u ∈ K` of `⟨f, v - u⟩ ≤ ⟨A u, v - u⟩` for every `v ∈ K`.

## Main declarations

* `EllipticPdes.IsHemicontinuousOp.strongVI_of_weakVI`: Minty's lemma.
* `EllipticPdes.IsMonotoneOp.weakVI_of_strongVI`: the converse.
* `EllipticPdes.IsMonotoneOp.sub_const`, `EllipticPdes.IsHemicontinuousOp.sub_const`,
  `EllipticPdes.IsCoerciveOp.sub_const`: the three properties remain true for `fun v => A v - f`.
* `EllipticPdes.exists_strongVI`: existence for a monotone hemicontinuous coercive operator.
* `EllipticPdes.existsUnique_strongVI`: uniqueness under strict monotonicity.
-/

@[expose] public section

open Set Filter Topology

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {K : Set X}
  {A : X → StrongDual ℝ X}

/-- **Minty's lemma** (Ferreira–Gomes–Üçer, Remark 2.17, p. 12). On a convex set, a hemicontinuous
operator that satisfies the weak inequality `0 ≤ ⟨A v, v - u⟩` at `u ∈ K` satisfies the strong
inequality `0 ≤ ⟨A u, v - u⟩`. -/
theorem IsHemicontinuousOp.strongVI_of_weakVI (hK : Convex ℝ K) (hA : IsHemicontinuousOp K A)
    {u : X} (hu : u ∈ K) (h : ∀ v ∈ K, 0 ≤ A v (v - u)) : ∀ v ∈ K, 0 ≤ A u (v - u) := by
  intro v hv
  set φ : ℝ → ℝ := fun t => A ((1 - t) • u + t • v) (v - u) with hφ
  have hcont : ContinuousWithinAt φ (Ioc 0 1) 0 :=
    ((hA u hu v hv (v - u)).continuousWithinAt
      (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)).mono Ioc_subset_Icc_self
  have hpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ φ t := by
    intro t ht
    have hmem : (1 - t) • u + t • v ∈ K :=
      hK hu hv (by linarith [ht.2]) ht.1.le (by ring)
    have h1 := h _ hmem
    have h2 : (1 - t) • u + t • v - u = t • (v - u) := by
      module
    rw [h2, map_smul, smul_eq_mul] at h1
    exact nonneg_of_mul_nonneg_right h1 ht.1
  have hlim : Tendsto φ (𝓝[Ioc 0 1] 0) (𝓝 (φ 0)) := hcont
  have hne : (𝓝[Ioc (0 : ℝ) 1] 0).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have h0 : 0 ≤ φ 0 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hpos)
  simpa [hφ] using h0

/-- **Converse of Minty's lemma.** A monotone operator satisfies the weak inequality at any `u ∈ K`
that satisfies the strong one. -/
theorem IsMonotoneOp.weakVI_of_strongVI (hA : IsMonotoneOp K A) {u : X} (hu : u ∈ K)
    (h : ∀ v ∈ K, 0 ≤ A u (v - u)) : ∀ v ∈ K, 0 ≤ A v (v - u) := by
  intro v hv
  have h1 := hA v hv u hu
  have h2 := h v hv
  simp only [sub_apply] at h1
  linarith

/-- Strict monotonicity implies monotonicity. -/
theorem IsStrictlyMonotoneOp.isMonotoneOp (hA : IsStrictlyMonotoneOp K A) : IsMonotoneOp K A := by
  intro u hu v hv
  by_cases huv : u = v
  · subst huv
    simp
  · exact (hA u hu v hv huv).le

/-- Subtracting a datum `f` keeps monotonicity. -/
theorem IsMonotoneOp.sub_const (hA : IsMonotoneOp K A) (f : StrongDual ℝ X) :
    IsMonotoneOp K (fun v => A v - f) := by
  intro u hu v hv
  simpa [sub_sub_sub_cancel_right] using hA u hu v hv

/-- Subtracting a datum `f` keeps hemicontinuity. -/
theorem IsHemicontinuousOp.sub_const (hA : IsHemicontinuousOp K A) (f : StrongDual ℝ X) :
    IsHemicontinuousOp K (fun v => A v - f) := by
  intro u hu v hv w
  have := (hA u hu v hv w).sub (continuousOn_const (c := f w))
  refine this.congr (fun t _ => ?_)
  simp [sub_apply]

/-- Subtracting a datum `f` keeps coercivity, with the same base point. -/
theorem IsCoerciveOp.sub_const (hA : IsCoerciveOp K A) (f : StrongDual ℝ X) :
    IsCoerciveOp K (fun v => A v - f) := by
  obtain ⟨v₀, hv₀, h⟩ := hA
  refine ⟨v₀, hv₀, ?_⟩
  simpa [sub_sub_sub_cancel_right] using h

/-- **Lions–Stampacchia theorem** (Ferreira–Gomes–Üçer, Theorem 2.16 with Remark 2.17, pp. 11–12).
A monotone, hemicontinuous, coercive operator on a closed convex set `K` of a reflexive Banach
space has, for each `f ∈ X*`, a point `u ∈ K` that satisfies `⟨f, v - u⟩ ≤ ⟨A u, v - u⟩` for all
`v ∈ K`. -/
theorem exists_strongVI [CompleteSpace X] (hX : Analysis.IsReflexive X) (hK : Convex ℝ K)
    (hKc : IsClosed K) (hA : IsMonotoneOp K A) (hh : IsHemicontinuousOp K A)
    (hco : IsCoerciveOp K A) (f : StrongDual ℝ X) :
    ∃ u ∈ K, ∀ v ∈ K, f (v - u) ≤ A u (v - u) := by
  obtain ⟨u, hu, h⟩ := exists_weakVI hX hK hKc (hA.sub_const f) (hco.sub_const f)
  refine ⟨u, hu, fun v hv => ?_⟩
  have := (hh.sub_const f).strongVI_of_weakVI hK hu h v hv
  simp only [sub_apply] at this
  linarith

/-- **Uniqueness in the Lions–Stampacchia theorem.** Under strict monotonicity the solution is
unique. -/
theorem existsUnique_strongVI [CompleteSpace X] (hX : Analysis.IsReflexive X) (hK : Convex ℝ K)
    (hKc : IsClosed K) (hA : IsStrictlyMonotoneOp K A) (hh : IsHemicontinuousOp K A)
    (hco : IsCoerciveOp K A) (f : StrongDual ℝ X) :
    ∃! u, u ∈ K ∧ ∀ v ∈ K, f (v - u) ≤ A u (v - u) := by
  obtain ⟨u, hu, h⟩ := exists_strongVI hX hK hKc hA.isMonotoneOp hh hco f
  refine ⟨u, ⟨hu, h⟩, fun w ⟨hw, hwv⟩ => ?_⟩
  by_contra hne
  have h1 := h w hw
  have h2 := hwv u hu
  have h3 := hA w hw u hu hne
  simp only [sub_apply] at h3
  have e : u - w = -(w - u) := by abel
  rw [e, map_neg, map_neg] at h2
  linarith

end EllipticPdes
