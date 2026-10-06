/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.DifferenceQuotient

/-!
# Half-ball and tangential directions

The special case of the boundary `H²` estimate (Evans, *Partial Differential Equations*
(2nd ed.), §6.3.2, Theorem 4, proof steps 1–5) is set on the half-ball
`U = B^0(0, 1) ∩ ℝ^n_+` with the smaller half-ball `V := B^0(0, 1/2) ∩ ℝ^n_+` as the region
where the estimate is proved. This file provides that geometry: the half-ball as a set,
its openness (hence measurability), its interior and closure, and the fact that a
*tangential* translation of a point in the smaller half-ball stays in the larger one at a
small enough parameter: the geometric fact that makes the difference-quotient method run
in directions parallel to the flat boundary, exactly as `hshift`-translation staying inside
a compact-in-open pair (`EllipticPdes.Regularity.exists_margin_of_isCompact_subset_isOpen`,
`Regularity/CutoffTower.lean`) makes it run in the interior.

Coordinate `0` plays the role of Evans' outward normal direction `x_n`, matching Mathlib's
convention for `EuclideanHalfSpace`. Tangential directions are then `k.succ` for `k : Fin d`,
since `Fin.succ` is exactly the injection `Fin d → Fin (d + 1)` missing `0`.

## Main declarations

* `halfBall d r`: the open half-ball of radius `r` in `ℝ^{d+1}`.
* `isOpen_halfBall`, `measurableSet_halfBall`, `interior_halfBall`, `closure_halfBall`.
* `tangential_add_hshift_mem_halfBall`: a tangential translation of a point in the half-ball
  `V := halfBall d (r / 2)` stays in `U := halfBall d r`, for any step below the margin
  `r / 2`: the coordinate-`0` value is untouched by a tangential shift, so this is exact
  geometry, not a compactness-derived margin.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace EllipticPdes.Regularity

/-! ### Half-ball -/

/-- The open half-ball of radius `r` centred at the origin in `ℝ^{d+1}`: the metric ball
intersected with the open coordinate half-space `{x | 0 < x 0}`. Coordinate `0` is the
outward normal direction (Evans' `x_n`), matching Mathlib's `EuclideanHalfSpace`
convention. -/
def halfBall (d : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
  Metric.ball 0 r ∩ {x | 0 < x 0}

/-- The half-ball is open: the intersection of the open metric ball and the open coordinate
half-space `{x | 0 < x 0}`. -/
theorem isOpen_halfBall (d : ℕ) (r : ℝ) : IsOpen (halfBall d r) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))

/-- The half-ball is measurable. -/
theorem measurableSet_halfBall (d : ℕ) (r : ℝ) : MeasurableSet (halfBall d r) :=
  (isOpen_halfBall d r).measurableSet

/-- The half-ball is its own interior. -/
@[simp] theorem interior_halfBall (d : ℕ) (r : ℝ) : interior (halfBall d r) = halfBall d r :=
  (isOpen_halfBall d r).interior_eq

/-! ### Closure of the half-ball -/

/-- **Closure of the half-ball.** The closure of the open half-ball of radius `r` is the closed
ball intersected with the closed coordinate half-space `{x | 0 ≤ x 0}`: the half-ball is the
interior of that convex set, and the closure of the interior of a convex set with nonempty
interior is its closure. -/
theorem closure_halfBall (d : ℕ) {r : ℝ} (hr : 0 < r) :
    closure (halfBall d r) = Metric.closedBall 0 r ∩ {x | 0 ≤ x 0} := by
  let ℓ : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hconv : Convex ℝ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) r
      ∩ {x | 0 ≤ x 0}) :=
    (convex_closedBall _ _).inter (convex_halfSpace_ge ℓ.toLinearMap.isLinear 0)
  have hint : interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) r
      ∩ {x | 0 ≤ x 0}) = halfBall d r := by
    have h2 : interior {x : EuclideanSpace ℝ (Fin (d + 1)) | 0 ≤ x 0} = {x | 0 < x 0} := by
      have hℓ : Function.Surjective ℓ := fun a => ⟨EuclideanSpace.single 0 a, by simp [ℓ]⟩
      have := (ℓ.isOpenMap hℓ).preimage_interior_eq_interior_preimage ℓ.continuous
        (Set.Ici (0 : ℝ))
      simp [ℓ] at this
      exact this.symm
    rw [interior_inter, interior_closedBall _ hr.ne', h2]
    rfl
  have hne : (interior (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) r
      ∩ {x | 0 ≤ x 0})).Nonempty := by
    rw [hint]
    exact ⟨EuclideanSpace.single 0 (r / 2), by simp [halfBall, abs_of_pos hr]; linarith⟩
  have hclosed : IsClosed (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) r
      ∩ {x | 0 ≤ x 0}) :=
    Metric.isClosed_closedBall.inter (isClosed_le continuous_const ℓ.continuous)
  rw [← hint, hconv.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]

/-! ### Tangential directions -/

/-- **Tangential translation stays in the half-ball.** A translation in a *tangential*
direction `k.succ` (any coordinate other than the normal coordinate `0`) never changes the
normal coordinate: `(x + h • e_{k.succ}) 0 = x 0`. Consequently, for `x` in the smaller
half-ball `V := halfBall d (r / 2)` and any step `|h| < r / 2`, the translate stays in the
larger half-ball `U := halfBall d r`. This is the geometric fact underlying the boundary
`H²` estimate's difference-quotient step (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.2, Theorem 4, proof step 3): translating tangentially near the flat part of `∂U`
cannot cross it, unlike a translation in the normal direction. -/
theorem tangential_add_hshift_mem_halfBall (d : ℕ) (r : ℝ) (k : Fin d) {h : ℝ}
    (hh : |h| < r / 2) {x : EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ halfBall d (r / 2)) :
    x + hshift k.succ h ∈ halfBall d r := by
  have hcoord : (hshift k.succ h) (0 : Fin (d + 1)) = 0 := by
    simp [hshift, PiLp.smul_apply, (Fin.succ_ne_zero k).symm]
  refine ⟨?_, ?_⟩
  · change dist (x + hshift k.succ h) 0 < r
    rw [dist_eq_norm, sub_zero]
    have hxnorm : ‖x‖ < r / 2 := by
      have := hx.1
      simpa [dist_eq_norm] using this
    have hhnorm : ‖hshift k.succ h‖ = |h| := by simp [hshift, norm_smul]
    calc ‖x + hshift k.succ h‖ ≤ ‖x‖ + ‖hshift k.succ h‖ := norm_add_le _ _
      _ = ‖x‖ + |h| := by rw [hhnorm]
      _ < r / 2 + r / 2 := add_lt_add hxnorm hh
      _ = r := by ring
  · change (0:ℝ) < (x + hshift k.succ h) (0 : Fin (d + 1))
    rw [PiLp.add_apply, hcoord, add_zero]
    exact hx.2

end EllipticPdes.Regularity
