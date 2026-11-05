/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.ReflexiveCompact
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Direct method for convex functionals

Brezis (`brezis-2011-fun-ana-sob`, Corollary 3.23, p. 71) states that a convex, lower
semicontinuous and coercive functional on a non-empty closed convex subset of a reflexive Banach
space attains its minimum. The proof takes a sublevel set, which is convex, closed and bounded,
hence weakly compact. A convex lower semicontinuous function has weakly closed sublevel sets, so
it is weakly lower semicontinuous and attains its infimum on that compact set.

## Main declarations

* `EllipticPdes.exists_isMinOn_of_convex_of_bounded`: the minimum exists on a bounded closed
  convex set.
* `EllipticPdes.exists_isMinOn_of_convex`: the minimum exists on a closed convex set when the
  functional is coercive.
-/

@[expose] public section

open Filter Topology

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Direct method on bounded sets.** A convex lower semicontinuous function attains its minimum
on a non-empty bounded closed convex subset of a reflexive Banach space (Brezis, Corollary 3.23,
p. 71). Convexity of `K` comes from `ConvexOn ℝ K J`. `K.Nonempty` is required: on `K = ∅`
the conclusion `∃ u ∈ K, ...` is false. -/
theorem exists_isMinOn_of_convex_of_bounded (hX : Analysis.IsReflexive X) {K : Set X}
    (hKcl : IsClosed K) (hKne : K.Nonempty) {J : X → ℝ}
    (hJc : ConvexOn ℝ K J) (hJl : LowerSemicontinuousOn J K) (hKb : Bornology.IsBounded K) :
    ∃ u ∈ K, IsMinOn J K u := by
  set e := toWeakSpace ℝ X with he
  have hS : IsCompact (e '' K) :=
    isCompact_toWeakSpace_of_bounded_convex_closed hX hJc.1 hKcl hKb
  have hlsc : LowerSemicontinuousOn (fun y => J (e.symm y)) (e '' K) := by
    rw [lowerSemicontinuousOn_iff_preimage_Iic]
    intro b
    obtain ⟨v, hv, hveq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hJl b
    have hclosed : IsClosed {x ∈ K | J x ≤ b} := by
      have : {x ∈ K | J x ≤ b} = K ∩ v := by
        rw [← hveq]; rfl
      rw [this]; exact hKcl.inter hv
    refine ⟨e '' {x ∈ K | J x ≤ b}, isClosed_toWeakSpace_of_convex (hJc.convex_le b) hclosed, ?_⟩
    have hsub : e '' {x ∈ K | J x ≤ b} ⊆ e '' K := Set.image_mono (fun x hx => hx.1)
    ext y
    constructor
    · rintro ⟨hyK, hy⟩
      obtain ⟨x, hx, rfl⟩ := hyK
      exact ⟨⟨x, hx, rfl⟩, ⟨x, ⟨hx, by simpa using hy⟩, rfl⟩⟩
    · rintro ⟨hyK, hy⟩
      refine ⟨hyK, ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx.2
  obtain ⟨y, ⟨u, hu, rfl⟩, hmin⟩ := hlsc.exists_isMinOn (hKne.image e) hS
  refine ⟨u, hu, fun v hv => ?_⟩
  simpa using hmin ⟨v, hv, rfl⟩

/-- **Direct method.** A convex, lower semicontinuous and coercive function attains its minimum on
a non-empty closed convex subset of a reflexive Banach space (Brezis, Corollary 3.23, p. 71).
Convexity of `K` comes from `ConvexOn ℝ K J`. `K.Nonempty` is required: on `K = ∅`
the conclusion `∃ u ∈ K, ...` is false. -/
theorem exists_isMinOn_of_convex (hX : Analysis.IsReflexive X) {K : Set X}
    (hKcl : IsClosed K) (hKne : K.Nonempty) {J : X → ℝ}
    (hJc : ConvexOn ℝ K J) (hJl : LowerSemicontinuousOn J K)
    (hJco : Tendsto J (Bornology.cobounded X ⊓ 𝓟 K) atTop) : ∃ u ∈ K, IsMinOn J K u := by
  obtain ⟨v₀, hv₀⟩ := hKne
  set L : Set X := {x ∈ K | J x ≤ J v₀} with hL
  have hLsub : L ⊆ K := fun x hx => hx.1
  have hLcl : IsClosed L := by
    obtain ⟨v, hv, hveq⟩ := lowerSemicontinuousOn_iff_preimage_Iic.mp hJl (J v₀)
    have : L = K ∩ v := by rw [hL, ← hveq]; rfl
    rw [this]; exact hKcl.inter hv
  have hLb : Bornology.IsBounded L := by
    have h := (hJco.eventually (eventually_gt_atTop (J v₀)))
    rw [Filter.eventually_inf_principal] at h
    have hb : Bornology.IsBounded {x | x ∈ K → J v₀ < J x}ᶜ :=
      Bornology.isBounded_def.mpr (by rw [compl_compl]; exact h)
    refine hb.subset ?_
    rintro x ⟨hxK, hx⟩ hcon
    exact absurd (hcon hxK) (not_lt.mpr hx)
  obtain ⟨u, huL, hu⟩ := exists_isMinOn_of_convex_of_bounded hX hLcl
    ⟨v₀, hv₀, le_rfl⟩ (hJc.subset hLsub (hJc.convex_le (J v₀)))
    (hJl.mono hLsub) hLb
  refine ⟨u, huL.1, fun v hv => ?_⟩
  by_cases hle : J v ≤ J v₀
  · exact hu ⟨hv, hle⟩
  · exact (huL.2.trans (not_le.mp hle).le : J u ≤ J v)

end EllipticPdes
