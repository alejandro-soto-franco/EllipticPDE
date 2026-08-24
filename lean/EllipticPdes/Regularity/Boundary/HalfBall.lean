/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.DifferenceQuotient
import Mathlib.Geometry.Manifold.Instances.Real

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
own convention for `EuclideanHalfSpace` (`Mathlib.Geometry.Manifold.Instances.Real`), the
model space for manifolds with boundary: `EuclideanHalfSpace n := {x : EuclideanSpace ℝ
(Fin n) // 0 ≤ x 0}`. Tangential directions are then `k.succ` for `k : Fin d`, since
`Fin.succ` is exactly the injection `Fin d → Fin (d + 1)` missing `0`.

## Main declarations

* `halfBall d r`: the open half-ball of radius `r` in `ℝ^{d+1}`.
* `isOpen_halfBall`, `measurableSet_halfBall`, `interior_halfBall`, `closure_halfBall`.
* `tangential_add_hshift_mem_halfBall`: a tangential translation of a point in the half-ball
  `V := halfBall d (r / 2)` stays in `U := halfBall d r`, for any step below the margin
  `r / 2`: the coordinate-`0` value is untouched by a tangential shift, so this is exact
  geometry, not a compactness-derived margin.
-/

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

/-- **Closure of the half-ball.** The closure of the open half-ball of radius `r` is the
closed ball intersected with the closed coordinate half-space `{x | 0 ≤ x 0}`. The inclusion
`⊆` is immediate from monotonicity of closure against a closed superset; the inclusion `⊇`
exhibits, for a boundary point `x` (on the sphere, on the flat coordinate hyperplane, or
both), the explicit segment towards the interior witness `p₀ := (r/2) • e₀`, whose points
`(1 - t) x + t p₀` lie in the half-ball for every `t ∈ (0, 1]` and converge to `x` as
`t → 0`. -/
theorem closure_halfBall (d : ℕ) {r : ℝ} (hr : 0 < r) :
    closure (halfBall d r) = Metric.closedBall 0 r ∩ {x | 0 ≤ x 0} := by
  have hclosed : IsClosed (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) r
      ∩ {x | 0 ≤ x 0}) :=
    Metric.isClosed_closedBall.inter (isClosed_le continuous_const (by fun_prop))
  apply subset_antisymm
  · apply closure_minimal _ hclosed
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall] at hx ⊢
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  rintro x ⟨hxr, hx0⟩
  set p₀ : EuclideanSpace ℝ (Fin (d + 1)) := EuclideanSpace.single (0 : Fin (d + 1)) (r / 2)
    with hp₀def
  have hp₀norm : ‖p₀‖ = r / 2 := by
    rw [hp₀def, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < r / 2)]
  have hp₀coord : p₀ (0 : Fin (d + 1)) = r / 2 := by simp [hp₀def]
  have hxr' : ‖x‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hxr
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun n => (1 - 1 / ((n : ℝ) + 1)) • x + (1 / ((n : ℝ) + 1)) • p₀, fun n => ?_, ?_⟩
  · set t : ℝ := 1 / ((n : ℝ) + 1) with htdef
    have hnpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have ht0 : 0 < t := by rw [htdef]; positivity
    have ht1 : t ≤ 1 := by
      rw [htdef, div_le_one hnpos]; linarith [Nat.cast_nonneg (α := ℝ) n]
    refine ⟨?_, ?_⟩
    · -- membership in the metric ball of radius `r`
      change dist ((1 - t) • x + t • p₀) 0 < r
      rw [dist_eq_norm, sub_zero]
      have hstep1 : ‖(1 - t) • x + t • p₀‖ ≤ ‖(1 - t) • x‖ + ‖t • p₀‖ := norm_add_le _ _
      have hstep2 : ‖(1 - t) • x‖ = (1 - t) * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
      have hstep3 : ‖t • p₀‖ = t * (r / 2) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hp₀norm]
      have hstep4 : (1 - t) * ‖x‖ ≤ (1 - t) * r := mul_le_mul_of_nonneg_left hxr' (by linarith)
      nlinarith [hstep1, hstep2, hstep3, hstep4]
    · -- the coordinate-0 value stays strictly positive
      change (0:ℝ) < ((1 - t) • x + t • p₀) (0 : Fin (d + 1))
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hp₀coord]
      have h1 : (0:ℝ) ≤ (1 - t) * x (0 : Fin (d + 1)) := mul_nonneg (by linarith) hx0
      have h2 : (0:ℝ) < t * (r / 2) := mul_pos ht0 (by linarith)
      linarith
  · have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [tendsto_iff_dist_tendsto_zero]
    have hdist : (fun n : ℕ => dist ((1 - 1 / ((n : ℝ) + 1)) • x + (1 / ((n : ℝ) + 1)) • p₀) x)
        = fun n : ℕ => (1 / ((n : ℝ) + 1)) * ‖p₀ - x‖ := by
      funext n
      set t : ℝ := 1 / ((n : ℝ) + 1) with htdef
      have hexp : (1 - t) • x + t • p₀ - x = t • (p₀ - x) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [dist_eq_norm, hexp, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by rw [htdef]; positivity)]
    rw [hdist]
    simpa using hlim.mul_const ‖p₀ - x‖

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
