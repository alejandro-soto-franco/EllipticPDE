/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Interior

/-!
# Iterated weak derivatives on a region

The interior `H²` estimate `EllipticPdes.Regularity.interior_H2_estimate` produces one weak
derivative of one weak derivative, indexed by an explicit pair `(k, i)`. Higher regularity
iterates that step, so the pair has to become a list and the statement has to quantify over
its length. This file supplies the indexed object.

`HasIteratedWeakDerivOn V k u` names a family `D : List (Fin d) → L²(V)` with `D [] = u` and
each `D (l :: α)` a weak `l`-derivative of `D α`, for every list shorter than `k`. It is the
`L²`-level reading of `u ∈ H^k(V)`, carried as data rather than as an existential, so that a
proof can name a particular derivative and hand it on.

## Why a list of directions

The same choice as in `EllipticPdes.Regularity.IsWkInftyCoeff`, and for the same reason: one
step of the recursion is `cons`. A multi-index in `Fin d →₀ ℕ` would need equality of mixed
partials before the recursion could even be stated, and that equality is a theorem about the
family rather than part of its definition. Nothing here presumes it.

## Main declarations

* `HasIteratedWeakDerivOn`: weak derivatives up to order `k` on `V`, carried as a family.
* `HasIteratedWeakDerivOn.mono`: an order-`k` family is an order-`l` family for `l ≤ k`.
* `HasIteratedWeakDerivOn.deriv`: the order-`k` family of a first derivative, extracted from
  an order-`k+1` family by appending the direction on the right. This is the step the
  induction of Guo, *Partial Differential Equations I and II* (Course Lecture Notes),
  Theorem VIII.3.2 (p. 65) runs on.
* `IteratedL2Bound`: a uniform bound on every member of the family up to order `k`.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ} {V : Set (EuclideanSpace ℝ (Fin d))} {k l : ℕ}

/-- **Iterated weak derivatives on a region.** A family of `L²(V)` classes indexed by lists
of directions, with the empty list the function itself and each `cons` a weak derivative of
its parent. Carrying the family as data rather than asserting existence at each order lets a
consumer name `D [i, j]` and pass it on, which the induction of Guo, *Partial Differential
Equations I and II* (Course Lecture Notes), Theorem VIII.3.2 (p. 65) requires. -/
structure HasIteratedWeakDerivOn (V : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (u : L2D V)
    where
  /-- The chosen representative of the iterated weak derivative along a list of directions. -/
  D : List (Fin d) → L2D V
  /-- The empty list of directions is the function itself. -/
  D_nil : D [] = u
  /-- Each successive entry is a weak derivative of its parent, up to order `k`. -/
  D_step : ∀ (m : Fin d) (α : List (Fin d)), α.length < k →
    HasWeakDerivOn V m (D α) (D (m :: α))

namespace HasIteratedWeakDerivOn

variable {u : L2D V}

/-- Every `L²` class has weak derivatives up to order zero, vacuously: the family is constant
and `D_step` is asked of no list. -/
def zero (u : L2D V) : HasIteratedWeakDerivOn V 0 u where
  D := fun _ => u
  D_nil := rfl
  D_step := fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- An order-`k` family is an order-`l` family for every `l ≤ k`: the family is inherited and
`D_step` is asked of fewer lists. -/
def mono (hu : HasIteratedWeakDerivOn V k u) (hlk : l ≤ k) :
    HasIteratedWeakDerivOn V l u where
  D := hu.D
  D_nil := hu.D_nil
  D_step m α hα := hu.D_step m α (lt_of_lt_of_le hα hlk)

/-- **The induction step.** From weak derivatives up to order `k + 1` of `u`, the direction
`l` first derivative `D [l]` has weak derivatives up to order `k`, with family
`α ↦ D (α ++ [l])`. Appending on the right rather than consing on the left is what makes the
lengths line up: `(α ++ [l]).length < k + 1` is exactly `α.length < k`, so every step the new
family needs is a step the old family already has.

This is the reduction that turns Guo's Theorem VIII.3.2 into an induction on `k`: an
`H^{k+2}` conclusion for `u` is an `H^{k+1}` conclusion for each `∂_l u`, and `∂_l u` solves a
differentiated equation of the same form. -/
def deriv (hu : HasIteratedWeakDerivOn V (k + 1) u) (l : Fin d) :
    HasIteratedWeakDerivOn V k (hu.D [l]) where
  D := fun α => hu.D (α ++ [l])
  D_nil := by simp
  D_step m α hα := by
    have hlen : (α ++ [l]).length < k + 1 := by
      simpa [List.length_append] using Nat.succ_lt_succ hα
    simpa using hu.D_step m (α ++ [l]) hlen

/-- The order-one family of a function with derivatives to order `k + 1` records a weak
derivative in every direction. -/
theorem hasWeakDerivOn_D_singleton (hu : HasIteratedWeakDerivOn V (k + 1) u) (m : Fin d) :
    HasWeakDerivOn V m u (hu.D [m]) := by
  have h := hu.D_step m [] (Nat.succ_pos k)
  rwa [hu.D_nil] at h

end HasIteratedWeakDerivOn

/-- **A uniform `L²` bound on an iterated family.** Every derivative up to order `k` is
bounded by `C` in `L²(V)`. Kept apart from `HasIteratedWeakDerivOn` so that existence and
estimate can be proved and consumed separately, matching the shape of
`interior_H2_estimate`, which returns the derivative and its bound as separate conjuncts. -/
def IteratedL2Bound {u : L2D V} (hu : HasIteratedWeakDerivOn V k u) (C : ℝ) : Prop :=
  ∀ α : List (Fin d), α.length ≤ k → ‖hu.D α‖ ≤ C

namespace IteratedL2Bound

variable {u : L2D V} {C C' : ℝ}

/-- A bound at order `k` bounds the function itself. -/
theorem norm_le {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C) : ‖u‖ ≤ C := by
  have h := hC [] (Nat.zero_le k)
  rwa [hu.D_nil] at h

/-- A bound is inherited by any larger constant. -/
theorem mono_const {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C)
    (hCC : C ≤ C') : IteratedL2Bound hu C' := fun α hα => (hC α hα).trans hCC

/-- A bound at order `k` restricts to a bound on the order-`l` family for `l ≤ k`. -/
theorem mono_order {hu : HasIteratedWeakDerivOn V k u} (hC : IteratedL2Bound hu C)
    (hlk : l ≤ k) : IteratedL2Bound (hu.mono hlk) C := fun α hα => hC α (hα.trans hlk)

end IteratedL2Bound

end EllipticPdes.Regularity
