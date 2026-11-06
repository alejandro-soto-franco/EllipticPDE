/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.LionsStampacchia

/-!
# Browder–Minty theorem and Lax–Milgram without symmetry

On the whole space `K = univ` the Lions–Stampacchia inequality
`⟨f, v - u⟩ ≤ ⟨A u, v - u⟩` at `v = u ± w` forces `⟨A u, w⟩ = ⟨f, w⟩` for every `w`.
Then `A u = f`. A monotone, hemicontinuous, coercive operator on a reflexive Banach space is
therefore onto, and a strictly monotone one is a bijection (Brezis, `brezis-2011-fun-ana-sob`,
Theorem 5.16 (Minty–Browder), p. 145). A bounded bilinear form `B` with
`c ‖u‖ ^ 2 ≤ B u u` gives a strictly monotone, continuous and coercive operator `u ↦ B u`. This
yields the Lax–Milgram theorem (Brezis, Corollary 5.8, p. 140) with no symmetry hypothesis. The
coercivity `c ‖u‖ ^ 2 ≤ B u u` makes the symmetric part of `B` an inner product with an equivalent
norm, so a space with such a `B` is isomorphic to a Hilbert space. The statement needs no
chosen inner product, and covers no space beyond the Hilbertian ones.

## Main declarations

* `EllipticPdes.surjective_of_monotone`: the Browder–Minty theorem, existence.
* `EllipticPdes.bijective_of_strictlyMonotone`: the Browder–Minty theorem, with uniqueness.
* `EllipticPdes.laxMilgram_of_reflexive`: Lax–Milgram for a coercive bounded bilinear form, with
  the space assumed reflexive in place of a chosen inner product.
-/

@[expose] public section

open Set Filter Topology

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : X → StrongDual ℝ X}

/-- **Existence in the Browder–Minty theorem.** A monotone, hemicontinuous and coercive operator
on a reflexive Banach space is onto the dual (Brezis, Theorem 5.16, p. 145). -/
theorem surjective_of_monotone (hX : Analysis.IsReflexive X)
    (hA : IsMonotoneOp Set.univ A) (hh : IsHemicontinuousOp Set.univ A)
    (hco : IsCoerciveOp Set.univ A) : Function.Surjective A := by
  intro f
  obtain ⟨u, -, h⟩ := exists_strongVI hX convex_univ isClosed_univ hA hh hco f
  refine ⟨u, ?_⟩
  ext w
  have h1 := h (u + w) (mem_univ _)
  have h2 := h (u - w) (mem_univ _)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg] at h1 h2
  linarith

/-- **Bijectivity in the Browder–Minty theorem.** A strictly monotone, hemicontinuous and coercive
operator on a reflexive Banach space is a bijection onto the dual (Brezis, Theorem 5.16,
p. 145). -/
theorem bijective_of_strictlyMonotone (hX : Analysis.IsReflexive X)
    (hA : IsStrictlyMonotoneOp Set.univ A) (hh : IsHemicontinuousOp Set.univ A)
    (hco : IsCoerciveOp Set.univ A) : Function.Bijective A := by
  refine ⟨fun u v huv => ?_, surjective_of_monotone hX hA.isMonotoneOp hh hco⟩
  by_contra hne
  have := hA u (mem_univ _) v (mem_univ _) hne
  simp [huv] at this

/-- **Lax–Milgram theorem without symmetry** on a reflexive Banach space. A bounded bilinear
form `B` with `c ‖u‖ ^ 2 ≤ B u u` and `0 < c` has, for each `f` in the dual, a unique `u` with
`B u = f` (compare Brezis, Corollary 5.8, p. 140, for a Hilbert space). -/
theorem laxMilgram_of_reflexive (hX : Analysis.IsReflexive X)
    (B : X →L[ℝ] X →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (hB : ∀ u, c * ‖u‖ ^ 2 ≤ B u u)
    (f : StrongDual ℝ X) : ∃! u, B u = f := by
  have hsm : IsStrictlyMonotoneOp Set.univ (fun u => B u) := by
    intro u _ v _ huv
    have h : (B u - B v) (u - v) = B (u - v) (u - v) := by simp [map_sub]
    rw [h]
    have hn : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    exact lt_of_lt_of_le (by positivity) (hB (u - v))
  have hh : IsHemicontinuousOp Set.univ (fun u => B u) := by
    intro u _ v _ w
    have h1 : Continuous fun x : X => B x w :=
      (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp B.continuous
    have h2 : Continuous fun t : ℝ => (1 - t) • u + t • v := by fun_prop
    exact (h1.comp h2).continuousOn
  have hco : IsCoerciveOp Set.univ (fun u => B u) := by
    refine ⟨0, mem_univ _, ?_⟩
    have hlim : Tendsto (fun v : X => c * ‖v‖) (Bornology.cobounded X ⊓ 𝓟 Set.univ) atTop :=
      (tendsto_norm_cobounded_atTop.const_mul_atTop hc).mono_left inf_le_left
    refine tendsto_atTop_mono' _ ?_ hlim
    have hev : ∀ᶠ v : X in Bornology.cobounded X ⊓ 𝓟 Set.univ, 1 ≤ ‖v‖ :=
      (tendsto_norm_cobounded_atTop.eventually_ge_atTop 1).filter_mono inf_le_left
    filter_upwards [hev] with v hv
    have hpos : 0 < ‖v‖ := by linarith
    simp only [map_zero, sub_zero]
    rw [le_div_iff₀ hpos]
    nlinarith [hB v]
  exact (bijective_of_strictlyMonotone hX hsm hh hco).existsUnique f

end EllipticPdes
