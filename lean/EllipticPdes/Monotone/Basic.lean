/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Monotone operators

Ferreira–Gomes–Üçer (`ferreira-2025-sol-mea-gam`, Definition 2.15, p. 11) study an operator `A` from
a real normed space `X` into its dual through the pairing `⟨A u, v⟩`, and call it monotone, coercive
or hemicontinuous by the behaviour of that pairing. This file states each notion for a map `A : X →
StrongDual ℝ X` on a set `K ⊆ X`. The names end in `Op` so that they stay distinct from Mathlib's
order-theoretic `Monotone` and `MonotoneOn`.

## Main declarations

* `EllipticPdes.IsMonotoneOp`: `0 ≤ ⟨A u - A v, u - v⟩` for `u`, `v` in `K`.
* `EllipticPdes.IsStrictlyMonotoneOp`: the inequality is strict for `u ≠ v`.
* `EllipticPdes.IsStrictlyMonotoneOp.isMonotoneOp`: strict monotonicity implies monotonicity.
* `EllipticPdes.IsCoerciveOp`: `⟨A v - A v₀, v - v₀⟩ / ‖v‖` tends to infinity along `K`.
* `EllipticPdes.IsHemicontinuousOp`: `t ↦ ⟨A ((1 - t) u + t v), w⟩` is continuous on `[0, 1]`.
* `EllipticPdes.IsMonotoneOp.of_bilin`: a bounded bilinear form with `0 ≤ B u u` is monotone.
-/

@[expose] public section

open Filter Topology

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- An operator `A : X → X*` is monotone on `K` when `0 ≤ ⟨A u - A v, u - v⟩` for all `u`, `v`
in `K` (Ferreira–Gomes–Üçer, Definition 2.15(a), p. 11). -/
def IsMonotoneOp (K : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, 0 ≤ (A u - A v) (u - v)

/-- An operator `A : X → X*` is strictly monotone on `K` when `0 < ⟨A u - A v, u - v⟩` for all
distinct `u`, `v` in `K`. This is the strict form of Ferreira–Gomes–Üçer, Definition 2.15(a),
p. 11. -/
def IsStrictlyMonotoneOp (K : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → 0 < (A u - A v) (u - v)

/-- Strict monotonicity implies monotonicity. -/
theorem IsStrictlyMonotoneOp.isMonotoneOp {K : Set X} {A : X → StrongDual ℝ X}
    (hA : IsStrictlyMonotoneOp K A) : IsMonotoneOp K A := by
  intro u hu v hv
  by_cases huv : u = v
  · subst huv
    simp
  · exact (hA u hu v hv huv).le

/-- An operator `A : X → X*` is coercive on `K` when some `v₀ ∈ K` makes
`⟨A v - A v₀, v - v₀⟩ / ‖v‖` tend to infinity as `‖v‖ → ∞` within `K`. The filter is
`cobounded X ⊓ 𝓟 K` and the quotient is plain real division (Ferreira–Gomes–Üçer,
Definition 2.15(b), p. 11). On a bounded `K` the filter is trivial, so the condition holds
vacuously and the coercive existence theorem contains the bounded one. -/
def IsCoerciveOp (K : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∃ v₀ ∈ K, Tendsto (fun v => (A v - A v₀) (v - v₀) / ‖v‖)
    (Bornology.cobounded X ⊓ 𝓟 K) atTop

/-- An operator `A : X → X*` is hemicontinuous on `K` when `t ↦ ⟨A ((1 - t) u + t v), w⟩` is
continuous on `[0, 1]` for all `u`, `v` in `K` and all `w` in `X` (Ferreira–Gomes–Üçer,
Definition 2.15(c), p. 11). -/
def IsHemicontinuousOp (K : Set X) (A : X → StrongDual ℝ X) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ w : X,
    ContinuousOn (fun t : ℝ => A ((1 - t) • u + t • v) w) (Set.Icc 0 1)

/-- A bounded bilinear form `B` with `0 ≤ B u u` gives the monotone operator `u ↦ B u` on the
whole space, since `⟨B u - B v, u - v⟩ = B (u - v) (u - v)` by bilinearity. -/
theorem IsMonotoneOp.of_bilin (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : ∀ u, 0 ≤ B u u) :
    IsMonotoneOp Set.univ (fun u => B u) := by
  intro u _ v _
  have h : (B u - B v) (u - v) = B (u - v) (u - v) := by simp [map_sub]
  rw [h]
  exact hB (u - v)

example {K : Set X} {A : X → StrongDual ℝ X} {u v : X} (h : IsMonotoneOp K A) (hu : u ∈ K)
    (hv : v ∈ K) : 0 ≤ (A u - A v) (u - v) := h u hu v hv

end EllipticPdes
