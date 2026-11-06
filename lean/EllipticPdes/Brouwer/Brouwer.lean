/-
Copyright (c) 2026 harfe. Released under the MIT licence; see LICENSE-fixed-point-theorems.
Copied from https://github.com/harfe/fixed-point-theorems-lean4 at 93a3eed3364281a9dbf9652bb52356a8db65057c
and placed in the namespace `EllipticPdes.Brouwer`. Modifications: namespacing and import paths.
-/

module

public import EllipticPdes.Brouwer.ApplyCubicalSperner
public import EllipticPdes.Brouwer.ConvexHomeos
public import Mathlib.Dynamics.FixedPoints.Basic

set_option linter.style.header false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false
set_option linter.style.show false
set_option linter.style.dollarSyntax false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# Brouwer's fixed-point theorem

Every continuous self-map of a nonempty compact convex subset of a finite-dimensional real normed
space has a fixed point.
-/

@[expose] public section

namespace EllipticPdes.Brouwer

/- Brouwer fixed-point theorem:
Every continuous function mapping a nonempty compact convex set to itself has a fixed point
(the set should be a subset of a finite dimensional vector space).

https://en.wikipedia.org/wiki/Brouwer_fixed-point_theorem
-/


theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    : ∀ (s : Set V), Convex ℝ s → IsCompact s → Set.Nonempty s →
    ∀ (f : C(s, s)), ∃ x, f x = x := by {
  intro s hcvx hcmpct hne f
  obtain ⟨k, ⟨e⟩ ⟩ := homeo_unit_cube_of_convex_compact s hcvx hcmpct hne
  let g := (toContinuousMap e).comp (f.comp (toContinuousMap e.symm))
  obtain ⟨y, hy⟩ := @fixed_point_unit_cube k g
  use (toContinuousMap e.symm) y
  have h1 : e.symm (e (f (e.symm y))) = e.symm y := congrArg e.symm hy
  rwa [e.symm_apply_apply] at h1
}

/-- Brouwer's fixed-point theorem stated with mathlib's `Function.IsFixedPt` vocabulary. -/
theorem brouwer_fixed_point_isFixedPt {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    ∃ x, Function.IsFixedPt f x := by
  simpa [Function.IsFixedPt] using brouwer_fixed_point s hcvx hcmpct hne f

/-- The fixed-point set of a continuous self-map on a Brouwer domain is nonempty. -/
theorem brouwer_fixedPoints_nonempty {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) (hcvx : Convex ℝ s) (hcmpct : IsCompact s) (hne : Set.Nonempty s)
    (f : C(s, s)) :
    (Function.fixedPoints f).Nonempty := by
  exact brouwer_fixed_point_isFixedPt s hcvx hcmpct hne f

end EllipticPdes.Brouwer
