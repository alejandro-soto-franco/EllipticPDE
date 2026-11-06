/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.C1Boundary
public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Invariance of a `C¹` boundary under a linear equivalence

A domain with `C¹` boundary keeps a `C¹` boundary under every continuous linear equivalence of
`ℝᵈ`, isometric or not. Near a boundary point the domain is the positive set of a `C¹` function
with nonzero derivative, and after a linear map it still is. The graph lemma turns such a set back
into the region above a `C¹` graph: the implicit function theorem gives the graph near the point,
monotonicity along the graph direction identifies the positive set with the region above it, and a
cutoff in the tangential directions makes the graph globally `C¹`.

## Main declarations

* `EllipticPdes.Extension.exists_aboveGraph_of_fderiv_pos`: the positive set of a `C¹` function
  with positive derivative along `eⱼ` at a zero is, near that zero, the region above a `C¹` graph
  independent of the `j`-th coordinate.
* `EllipticPdes.Extension.C1Chart.graph_motion_eq_of_mem_frontier`: a chart's graph passes through
  the boundary point it describes.
* `EllipticPdes.Extension.HasC1Boundary.image_linearEquiv`: invariance under a continuous linear
  equivalence of `ℝᵈ`.
* `EllipticPdes.Extension.HasC1BoundaryNormed`: `C¹` boundary in a finite-dimensional real normed
  space, with `hasC1BoundaryNormed_iff` and `HasC1BoundaryNormed.image_linearEquiv`.
-/

@[expose] public section

open Metric Set Filter
open scoped Topology

noncomputable section

namespace EllipticPdes.Extension

variable {d : ℕ}

/-! ### The tangential projection and the `j`-th coordinate -/

section Projection

variable (j : Fin d)

/-- The projection is idempotent. -/
theorem tangential_tangential (y : EuclideanSpace ℝ (Fin d)) :
    tangential j (tangential j y) = tangential j y := by
  ext i
  simp only [tangential_coord]
  split_ifs <;> rfl

/-- A point is its tangential part plus its `j`-th coordinate along `eⱼ`. -/
theorem tangential_add_coord (y : EuclideanSpace ℝ (Fin d)) :
    tangential j y + y j • (EuclideanSpace.single j (1 : ℝ)) = y := by
  rw [tangential_apply, sub_add_cancel]

/-- The `j`-th coordinate of `tangential j y + t eⱼ` is `t`. -/
theorem coord_tangential_add_smul (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    (tangential j y + t • (EuclideanSpace.single j (1 : ℝ))) j = t := by
  simp [tangential_coord]

/-- The tangential part of `tangential j y + t eⱼ` is `tangential j y`. -/
theorem tangential_tangential_add_smul (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    tangential j (tangential j y + t • (EuclideanSpace.single j (1 : ℝ))) = tangential j y := by
  rw [tangential_add_smul, tangential_tangential]

/-- The distance from `tangential j y + p_j eⱼ` to `p` is the norm of the tangential part of
`y - p`. -/
theorem dist_tangential_add_coord (y p : EuclideanSpace ℝ (Fin d)) :
    dist (tangential j y + p j • (EuclideanSpace.single j (1 : ℝ))) p = ‖tangential j (y - p)‖ := by
  rw [dist_eq_norm, map_sub]
  congr 1
  nth_rewrite 2 [← tangential_add_coord j p]
  abel

/-- The affine parametrisation `(y, t) ↦ tangential j y + t eⱼ`. -/
def graphParam : EuclideanSpace ℝ (Fin d) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (tangential j).comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) ℝ) +
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) ℝ).smulRight
      (EuclideanSpace.single j (1 : ℝ))

theorem graphParam_apply (v : EuclideanSpace ℝ (Fin d) × ℝ) :
    graphParam j v = tangential j v.1 + v.2 • (EuclideanSpace.single j (1 : ℝ)) := rfl

end Projection

/-- A continuous linear endomorphism of `ℝ` that does not vanish at `1` is invertible. -/
theorem isInvertible_of_apply_one_ne_zero {g : ℝ →L[ℝ] ℝ} (h : g 1 ≠ 0) : g.IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse (g := (g 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.ext_ring (by simp [h]))
    (ContinuousLinearMap.ext_ring (by simp [h]))

/-! ### The implicit graph -/

section ImplicitGraph

variable {j : Fin d} {H : EuclideanSpace ℝ (Fin d) → ℝ} {p : EuclideanSpace ℝ (Fin d)}

/-- The parametrised function `(y, t) ↦ H (tangential j y + t eⱼ)` is `C¹` at `(p, p_j)`. -/
theorem Internal.contDiffAt_param (hH : ContDiff ℝ 1 H) :
    ContDiffAt ℝ 1 (H ∘ graphParam j) (p, p j) :=
  (hH.comp (graphParam j).contDiff).contDiffAt

/-- The partial derivative in `t` of the parametrised function at `(p, p_j)`. -/
theorem Internal.fderiv_param_inr (hH : ContDiff ℝ 1 H) (s : ℝ) :
    (fderiv ℝ (H ∘ graphParam j) (p, p j) ∘L .inr ℝ (EuclideanSpace ℝ (Fin d)) ℝ) s =
      s * fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ)) := by
  rw [ContinuousLinearMap.comp_apply, fderiv_comp _ (hH.differentiable (by simp) _)
    (graphParam j).differentiableAt, (graphParam j).fderiv]
  simp [graphParam_apply, tangential_add_coord]

/-- The partial derivative in `t` is invertible. -/
theorem Internal.isInvertible_param (hH : ContDiff ℝ 1 H)
    (hpos : 0 < fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ))) :
    (fderiv ℝ (H ∘ graphParam j) (p, p j) ∘L .inr ℝ (EuclideanSpace ℝ (Fin d)) ℝ).IsInvertible :=
  isInvertible_of_apply_one_ne_zero (by rw [Internal.fderiv_param_inr hH]; simpa using hpos.ne')

/-- The implicit function of `(y, t) ↦ H (tangential j y + t eⱼ)` at `(p, p_j)`. -/
def implicitFn (hH : ContDiff ℝ 1 H) (hpos : 0 < fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ))) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  (Internal.contDiffAt_param (j := j) (p := p) hH).implicitFunction one_ne_zero
    (Internal.isInvertible_param hH hpos)

/-- **Implicit graph.** The implicit function read on the tangential part of `y`, so that it does
not depend on the `j`-th coordinate. -/
def implicitGraph (hH : ContDiff ℝ 1 H) (hpos : 0 < fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ)))
    (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  implicitFn hH hpos (tangential j y + p j • (EuclideanSpace.single j (1 : ℝ)))

variable (hH : ContDiff ℝ 1 H) (hpos : 0 < fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ)))

/-- The implicit graph does not depend on the `j`-th coordinate. -/
theorem indepCoord_implicitGraph : IndepCoord j (implicitGraph hH hpos) := fun y t => by
  simp only [implicitGraph, tangential_add_smul]

/-- The implicit graph passes through `p`. -/
theorem implicitGraph_self : implicitGraph hH hpos p = p j := by
  rw [implicitGraph, tangential_add_coord]
  exact ContDiffAt.implicitFunction_apply_self _ one_ne_zero _

/-- The implicit function is `C¹` on a ball about `p`. -/
theorem exists_ball_contDiffAt_implicitFn :
    ∃ δ > 0, ∀ z ∈ ball p δ, ContDiffAt ℝ 1 (implicitFn hH hpos) z :=
  Metric.eventually_nhds_iff_ball.1
    ((ContDiffAt.contDiffAt_implicitFunction (Internal.contDiffAt_param (j := j) (p := p) hH)
      one_ne_zero (Internal.isInvertible_param hH hpos)).eventually (by simp))

/-- The implicit graph is `C¹` at every point whose tangential distance to `p` is small. -/
theorem contDiffAt_implicitGraph {δ : ℝ}
    (hδ : ∀ z ∈ ball p δ, ContDiffAt ℝ 1 (implicitFn hH hpos) z) {y : EuclideanSpace ℝ (Fin d)}
    (hy : ‖tangential j (y - p)‖ < δ) : ContDiffAt ℝ 1 (implicitGraph hH hpos) y :=
  (hδ _ (by rw [mem_ball, dist_tangential_add_coord]; exact hy)).comp y
    ((tangential j).contDiff.add contDiff_const).contDiffAt

/-- **Zero set near `p`.** Near `p`, `H` vanishes exactly on the implicit graph. -/
theorem eventually_eq_zero_iff (hp : H p = 0) :
    ∀ᶠ y in 𝓝 p, (H y = 0 ↔ implicitGraph hH hpos y = y j) := by
  have hT : Tendsto (fun y : EuclideanSpace ℝ (Fin d) =>
      (tangential j y + p j • (EuclideanSpace.single j (1 : ℝ)), y j)) (𝓝 p) (𝓝 (p, p j)) := by
    refine (((tangential j).continuous.add continuous_const).prodMk
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous).tendsto' p _ ?_
    simp [tangential_add_coord]
  filter_upwards [hT.eventually (ContDiffAt.eventually_apply_eq_iff_implicitFunction
    (Internal.contDiffAt_param (j := j) (p := p) hH) one_ne_zero
      (Internal.isInvertible_param hH hpos))] with y hy
  simpa [implicitGraph, implicitFn, graphParam_apply, tangential_tangential_add_smul,
    tangential_add_coord, hp] using hy

/-- The parameters of the line through `a` along `eⱼ` that stay in a ball form a convex set. -/
theorem Internal.convex_line_preimage (j : Fin d) (a q : EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    Convex ℝ ((fun s : ℝ => a + s • EuclideanSpace.single j (1 : ℝ)) ⁻¹' ball q δ) := by
  convert (convex_ball q δ).affine_preimage
    (AffineMap.lineMap a (a + EuclideanSpace.single j (1 : ℝ))) using 1
  ext s
  simp [AffineMap.lineMap_apply, add_comm]

/-- The derivative of `H` along the line through `a` in the direction `eⱼ`. -/
theorem Internal.hasDerivAt_line (hH : ContDiff ℝ 1 H) (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => H (a + t • EuclideanSpace.single j (1 : ℝ)))
      (fderiv ℝ H (a + s • EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))
      s := by
  have h := (hH.differentiable (by simp) (a + s • EuclideanSpace.single j (1 : ℝ))).hasFDerivAt
    |>.comp_hasDerivAt
    s (((hasDerivAt_id s).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add a)
  simp only [id, one_smul] at h
  exact h

/-- `H` increases strictly along the line through `tangential j y` on the parameters where the
line stays in a ball on which `∂ⱼH > 0`. -/
theorem Internal.strictMonoOn_line (hH : ContDiff ℝ 1 H) {δ : ℝ}
    (hδ : ∀ z ∈ ball p δ, 0 < fderiv ℝ H z (EuclideanSpace.single j (1 : ℝ)))
    (a : EuclideanSpace ℝ (Fin d)) :
    StrictMonoOn (fun t : ℝ => H (a + t • EuclideanSpace.single j (1 : ℝ)))
      ((fun t : ℝ => a + t • EuclideanSpace.single j (1 : ℝ)) ⁻¹' ball p δ) :=
  strictMonoOn_of_deriv_pos (Internal.convex_line_preimage j _ p δ)
    (fun t _ => (Internal.hasDerivAt_line hH _ t).continuousAt.continuousWithinAt)
    fun t ht => (Internal.hasDerivAt_line hH _ t).deriv ▸ hδ _
      (interior_subset
        (s := (fun t : ℝ => a + t • EuclideanSpace.single j (1 : ℝ)) ⁻¹' ball p δ) ht)

/-- The `j`-th coordinate of `y` is a parameter of the line through `tangential j y` that lands in
any ball containing `y`. -/
theorem Internal.coord_mem_line_preimage {δ : ℝ} {y : EuclideanSpace ℝ (Fin d)}
    (hy : y ∈ ball p δ) :
    y j ∈ (fun t : ℝ => tangential j y + t • EuclideanSpace.single j (1 : ℝ)) ⁻¹' ball p δ := by
  change tangential j y + y j • EuclideanSpace.single j (1 : ℝ) ∈ ball p δ
  rwa [tangential_add_coord]

/-- **Positivity along a line of increase.** If `H` increases strictly along `eⱼ` on a ball that
contains `y` and the zero `tangential j y + c eⱼ`, then `H y > 0` exactly when `y_j > c`. -/
theorem Internal.pos_iff_of_fderiv_pos (hH : ContDiff ℝ 1 H) {δ : ℝ}
    (hδ : ∀ z ∈ ball p δ, 0 < fderiv ℝ H z (EuclideanSpace.single j (1 : ℝ)))
    {y : EuclideanSpace ℝ (Fin d)} {c : ℝ} (hy : y ∈ ball p δ)
    (hz : tangential j y + c • EuclideanSpace.single j (1 : ℝ) ∈ ball p δ)
    (hHz : H (tangential j y + c • EuclideanSpace.single j (1 : ℝ)) = 0) :
    0 < H y ↔ c < y j :=
  calc 0 < H y ↔ H (tangential j y + c • EuclideanSpace.single j (1 : ℝ)) <
        H (tangential j y + y j • EuclideanSpace.single j (1 : ℝ)) := by
          rw [hHz, tangential_add_coord]
    _ ↔ c < y j :=
        (Internal.strictMonoOn_line hH hδ _).lt_iff_lt hz (Internal.coord_mem_line_preimage hy)

include hH hpos in
/-- The derivative of `H` along `eⱼ` stays positive near `p`. -/
theorem eventually_fderiv_pos :
    ∀ᶠ z in 𝓝 p, 0 < fderiv ℝ H z (EuclideanSpace.single j (1 : ℝ)) :=
  (((hH.continuous_fderiv (by simp)).clm_apply continuous_const).tendsto p).eventually
    (lt_mem_nhds hpos)

/-- The implicit graph is continuous at `p`. -/
theorem continuousAt_implicitGraph : ContinuousAt (implicitGraph hH hpos) p := by
  obtain ⟨δ, hδ, h⟩ := exists_ball_contDiffAt_implicitFn hH hpos
  exact (contDiffAt_implicitGraph hH hpos h (by simpa using hδ)).continuousAt

/-- The point of the implicit graph above `tangential j y` tends to `p` as `y` does. -/
theorem Internal.tendsto_graphPoint :
    Tendsto (fun y => tangential j y + implicitGraph hH hpos y • EuclideanSpace.single j (1 : ℝ))
      (𝓝 p) (𝓝 p) := by
  have h : ContinuousAt (fun y => tangential j y + implicitGraph hH hpos y •
      EuclideanSpace.single j (1 : ℝ)) p :=
    (tangential j).continuous.continuousAt.add
      ((continuousAt_implicitGraph hH hpos).smul continuousAt_const)
  rwa [ContinuousAt, implicitGraph_self, tangential_add_coord] at h

/-- **Positive set near `p`.** Near `p`, `H` is positive exactly above the implicit graph. -/
theorem eventually_pos_iff (hp : H p = 0) :
    ∀ᶠ y in 𝓝 p, (0 < H y ↔ implicitGraph hH hpos y < y j) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((eventually_fderiv_pos hH hpos).and (eventually_eq_zero_iff hH hpos hp))
  filter_upwards [ball_mem_nhds p hδ,
    (Internal.tendsto_graphPoint hH hpos).eventually (ball_mem_nhds p hδ)] with y hy hzy
  refine Internal.pos_iff_of_fderiv_pos hH (fun z hz => (hball z hz).1) hy hzy
    ((hball _ hzy).2.2 ?_)
  rw [coord_tangential_add_smul, indepCoord_implicitGraph hH hpos,
    apply_tangential (indepCoord_implicitGraph hH hpos)]

/-- The bump vanishes at every point whose tangential distance to `p` is at least `2 r`. -/
theorem cylinderBump_eq_zero {r : ℝ} (hr : 0 < r) {y : EuclideanSpace ℝ (Fin d)}
    (hy : 2 * r ≤ ‖tangential j (y - p)‖) : cylinderBump j p hr y = 0 :=
  ContDiffBump.zero_of_le_dist _ (by rwa [dist_eq_norm, ← map_sub])

/-- **Cut-off implicit graph.** The implicit graph multiplied by the bump of radii `r` and `2 r`
in the tangential directions about `p`. -/
def cutGraph {r : ℝ} (hr : 0 < r) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  cylinderBump j p hr y * implicitGraph hH hpos y

/-- The cut-off graph is of class `C¹` once the bump lives where the implicit function is. -/
theorem contDiff_cutGraph {δ r : ℝ} (hδ : ∀ z ∈ ball p δ, ContDiffAt ℝ 1 (implicitFn hH hpos) z)
    (hr : 0 < r) (hrδ : 2 * r < δ) : ContDiff ℝ 1 (cutGraph hH hpos hr) := by
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : ‖tangential j (y - p)‖ < δ
  · exact ((contDiff_cylinderBump hr).of_le (by exact_mod_cast le_top)).contDiffAt.mul
      (contDiffAt_implicitGraph hH hpos hδ hy)
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const ((tangential j).continuous.norm.comp
      (continuous_id.sub continuous_const))).mem_nhds (show 2 * r < ‖tangential j (y - p)‖ by
        linarith [not_lt.1 hy])] with z hz
    exact (mul_eq_zero_of_left (cylinderBump_eq_zero hr (le_of_lt (by simpa using hz))) _)

/-- The cut-off graph does not depend on the `j`-th coordinate. -/
theorem indepCoord_cutGraph {r : ℝ} (hr : 0 < r) : IndepCoord j (cutGraph hH hpos hr) :=
  fun y t => by
    simp only [cutGraph, indepCoord_cylinderBump hr y t, indepCoord_implicitGraph hH hpos y t]

/-- On the ball of radius `r` the cut-off graph is the implicit graph. -/
theorem cutGraph_eq {r : ℝ} (hr : 0 < r) {y : EuclideanSpace ℝ (Fin d)} (hy : y ∈ ball p r) :
    cutGraph hH hpos hr y = implicitGraph hH hpos y := by
  rw [cutGraph, cylinderBump_eq_one hr hy, one_mul]

end ImplicitGraph

/-- **Graph lemma.** Let `H` be `C¹` with `H p = 0` and positive derivative at `p` along `eⱼ`.
Then near `p` the positive set of `H` is the region above a `C¹` graph that does not depend on the
`j`-th coordinate. -/
theorem exists_aboveGraph_of_fderiv_pos {j : Fin d} {H : EuclideanSpace ℝ (Fin d) → ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (hH : ContDiff ℝ 1 H) (hp : H p = 0)
    (hpos : 0 < fderiv ℝ H p (EuclideanSpace.single j (1 : ℝ))) :
    ∃ ρ > 0, ∃ γ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 γ ∧ IndepCoord j γ ∧
      {y | 0 < H y} ∩ ball p ρ = aboveGraph j γ ∩ ball p ρ := by
  obtain ⟨δ, hδ, hcd⟩ := exists_ball_contDiffAt_implicitFn hH hpos
  obtain ⟨ρ₀, hρ₀, hiff⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_pos_iff hH hpos hp)
  have hr : 0 < δ / 3 := by positivity
  refine ⟨min ρ₀ (δ / 3), lt_min hρ₀ hr, cutGraph hH hpos hr,
    contDiff_cutGraph hH hpos hcd hr (by linarith), indepCoord_cutGraph hH hpos hr, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, aboveGraph, and_congr_left_iff]
  intro hy
  rw [cutGraph_eq hH hpos hr (ball_subset_ball (min_le_right _ _) hy)]
  exact hiff y (ball_subset_ball (min_le_left _ _) hy)


/-! ### Boundary points and charts -/

namespace C1Chart

/-- **Boundary point on the chart's graph.** If the chart fits `Ω` at a boundary
point `x`, the moved point lies on the graph: on the region above the graph `x` would be interior,
below it `x` would be exterior. -/
theorem graph_motion_eq_of_mem_frontier (c : C1Chart d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {x : EuclideanSpace ℝ (Fin d)} (h : c.Fits Ω x) (hx : x ∈ frontier Ω) :
    c.graph (c.motion x) = c.motion x c.dir := by
  rcases lt_trichotomy (c.graph (c.motion x)) (c.motion x c.dir) with hlt | heq | hgt
  · refine absurd (mem_interior.2 ⟨_, fun z hz => ?_, (c.isOpen_region.preimage
      c.motion.continuous).inter isOpen_ball, ⟨hlt, mem_ball_self c.radius_pos⟩⟩) hx.2
    exact (show z ∈ Ω ∩ ball x c.radius by rw [c.fits_ball h]; exact hz).1
  · exact heq
  · obtain ⟨z, ⟨hzlt, hzb⟩, hzΩ⟩ := mem_closure_iff.1 hx.1
      ({z | c.motion z c.dir < c.graph (c.motion z)} ∩ ball x c.radius)
      ((isOpen_lt ((EuclideanSpace.proj c.dir : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp
        c.motion.continuous) (c.graph_differentiable.continuous.comp c.motion.continuous)).inter
        isOpen_ball) ⟨hgt, mem_ball_self c.radius_pos⟩
    exact (lt_asymm (a := c.graph (c.motion z)) (b := c.motion z c.dir)
      (show z ∈ (c.motion : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' c.region ∩
        ball x c.radius by rw [← c.fits_ball h]; exact ⟨hzΩ, hzb⟩).1 hzlt).elim

end C1Chart

section Image

variable (c : C1Chart d) (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d))

/-- The chart's motion after the inverse of `A`. -/
def chartMap : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (c.motion.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).comp
    (A.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))

/-- **Defining function of the image.** `G w = (M A⁻¹ w)_j - γ (M A⁻¹ w)`, positive exactly on the
moved region. -/
def chartFn (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  chartMap c A w c.dir - c.graph (chartMap c A w)

/-- The defining function is of class `C¹`. -/
theorem contDiff_chartFn : ContDiff ℝ 1 (chartFn c A) :=
  ((EuclideanSpace.proj c.dir : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.comp
    (chartMap c A).contDiff).sub (c.graph_contDiff.comp (chartMap c A).contDiff)

/-- The derivative of the defining function. -/
theorem hasFDerivAt_chartFn (x : EuclideanSpace ℝ (Fin d)) :
    HasFDerivAt (chartFn c A) (((EuclideanSpace.proj c.dir : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) -
      fderiv ℝ c.graph (chartMap c A x)).comp (chartMap c A)) x :=
  ((EuclideanSpace.proj c.dir : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).hasFDerivAt.sub
    (c.graph_differentiable _).hasFDerivAt).comp x (chartMap c A).hasFDerivAt

/-- The defining function has derivative `1` along `A M⁻¹ eⱼ`. -/
theorem fderiv_chartFn_apply (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (chartFn c A) x (A (c.motion.symm (EuclideanSpace.single c.dir (1 : ℝ)))) = 1 := by
  rw [(hasFDerivAt_chartFn c A x).fderiv]
  simp [chartMap, fderiv_apply_eq_zero_of_indepAlong c.graph_differentiable c.graph_indep]

/-- The derivative of the defining function never vanishes. -/
theorem fderiv_chartFn_ne_zero (x : EuclideanSpace ℝ (Fin d)) : fderiv ℝ (chartFn c A) x ≠ 0 :=
  fun h => one_ne_zero ((fderiv_chartFn_apply c A x).symm.trans (by rw [h]; rfl))

/-- The radius on which the image is described by the defining function. -/
def imageRadius : ℝ := c.radius / (‖(A.symm : EuclideanSpace ℝ (Fin d) →L[ℝ]
  EuclideanSpace ℝ (Fin d))‖ + 1)

theorem imageRadius_pos : 0 < imageRadius c A := by
  unfold imageRadius
  have := c.radius_pos
  positivity

/-- `A⁻¹` sends the ball of radius `imageRadius` about `A x` into the chart's ball about `x`. -/
theorem symm_mem_ball {x w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ ball (A x) (imageRadius c A)) :
    A.symm w ∈ ball x c.radius := by
  rw [mem_ball, dist_eq_norm, ← A.symm_apply_apply x, ← map_sub]
  set K := ‖(A.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖
  have hK : 0 < K + 1 := by positivity
  calc ‖A.symm (w - A x)‖ ≤ K * ‖w - A x‖ := A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ (K + 1) * ‖w - A x‖ := by gcongr; linarith
    _ < (K + 1) * imageRadius c A := by gcongr; rwa [← dist_eq_norm]
    _ = c.radius := by rw [imageRadius]; field_simp; ring

/-- **Image near `A x` as the positive set of the defining function.** -/
theorem image_inter_ball {Ω : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)}
    (h : c.Fits Ω x) :
    A '' Ω ∩ ball (A x) (imageRadius c A) =
      {w | 0 < chartFn c A w} ∩ ball (A x) (imageRadius c A) := by
  ext w
  simp only [mem_inter_iff, mem_ofPred_eq, and_congr_left_iff]
  intro hw
  rw [A.image_eq_preimage_symm, mem_preimage, chartFn, sub_pos]
  constructor
  · intro hΩ
    exact (show A.symm w ∈ _ ∩ ball x c.radius by
      rw [← c.fits_ball h]; exact ⟨hΩ, symm_mem_ball c A hw⟩).1
  · intro hpos
    exact (show A.symm w ∈ Ω ∩ ball x c.radius by
      rw [c.fits_ball h]; exact ⟨hpos, symm_mem_ball c A hw⟩).1

end Image

/-! ### A rotation onto a coordinate axis -/

/-- The Riesz vector of a nonzero covector is nonzero. -/
theorem Internal.riesz_ne_zero {ℓ : StrongDual ℝ (EuclideanSpace ℝ (Fin d))} (hℓ : ℓ ≠ 0) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ ≠ 0 :=
  fun h => hℓ ((InnerProductSpace.toDual ℝ _).symm.map_eq_zero_iff.1 h)

/-- The unit vector along `w` has the norm of `eⱼ`. -/
theorem Internal.norm_unit_eq {w : EuclideanSpace ℝ (Fin d)} (hw : w ≠ 0) (j : Fin d) :
    ‖‖w‖⁻¹ • w‖ = ‖EuclideanSpace.single j (1 : ℝ)‖ := by
  rw [PiLp.norm_single, norm_one]
  exact norm_smul_inv_norm hw

/-- The reflection exchanging a unit vector `n` with `eⱼ` sends `eⱼ` to `n`. -/
theorem Internal.reflection_single_eq {n : EuclideanSpace ℝ (Fin d)} (j : Fin d)
    (hn : ‖n‖ = ‖EuclideanSpace.single j (1 : ℝ)‖) :
    (ℝ ∙ (n - EuclideanSpace.single j (1 : ℝ)))ᗮ.reflection (EuclideanSpace.single j (1 : ℝ)) = n :=
  (congrArg _ (Submodule.reflection_sub hn)).symm.trans (Submodule.reflection_reflection _ n)

/-- A covector takes the value `‖w‖` on the unit vector along its Riesz vector `w`. -/
theorem Internal.apply_unit_riesz (ℓ : StrongDual ℝ (EuclideanSpace ℝ (Fin d))) :
    ℓ (‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ‖⁻¹ •
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ) =
      ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ‖ := by
  rw [← InnerProductSpace.toDual_symm_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- **Reflection turning a nonzero covector towards `eⱼ`.** For `ℓ ≠ 0` there is a linear
isometry `N` with `ℓ (N⁻¹ eⱼ) > 0`: the reflection exchanging `eⱼ` with the unit Riesz vector of
`ℓ`. -/
theorem exists_isometry_pos {ℓ : StrongDual ℝ (EuclideanSpace ℝ (Fin d))} (hℓ : ℓ ≠ 0)
    (j : Fin d) :
    ∃ N : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
      0 < ℓ (N.symm (EuclideanSpace.single j (1 : ℝ))) :=
  ⟨(ℝ ∙ (‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ‖⁻¹ •
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm ℓ -
        EuclideanSpace.single j (1 : ℝ)))ᗮ.reflection, by
    rw [Submodule.reflection_symm, Internal.reflection_single_eq j
      (Internal.norm_unit_eq (Internal.riesz_ne_zero hℓ) j), Internal.apply_unit_riesz]
    exact norm_pos_iff.2 (Internal.riesz_ne_zero hℓ)⟩

/-! ### Invariance -/

/-- The inverse of an isometry sends the ball about `N q` onto the ball about `q`. -/
theorem Internal.symm_mem_ball_isometry
    (N : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {q y : EuclideanSpace ℝ (Fin d)}
    {ρ : ℝ} (hy : y ∈ ball (N q) ρ) : N.symm y ∈ ball q ρ := by
  rwa [mem_ball, ← N.dist_map, N.apply_symm_apply]

/-- **Charts after an isometry.** If `S` agrees with the positive set of `G` near `q` and the
positive set of `G ∘ N⁻¹` agrees with a region above a graph near `N q`, then `N '' S` agrees with
that region near `N q`. -/
theorem image_isometry_inter_ball {S : Set (EuclideanSpace ℝ (Fin d))}
    {G : EuclideanSpace ℝ (Fin d) → ℝ} {q : EuclideanSpace ℝ (Fin d)}
    (N : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {j : Fin d}
    {γ : EuclideanSpace ℝ (Fin d) → ℝ} {ρ₀ ρ₁ : ℝ}
    (h₀ : S ∩ ball q ρ₀ = {w | 0 < G w} ∩ ball q ρ₀)
    (h₁ : {y | 0 < G (N.symm y)} ∩ ball (N q) ρ₁ = aboveGraph j γ ∩ ball (N q) ρ₁) :
    N '' S ∩ ball (N q) (min ρ₀ ρ₁) = aboveGraph j γ ∩ ball (N q) (min ρ₀ ρ₁) := by
  ext y
  simp only [mem_inter_iff, and_congr_left_iff]
  intro hy
  have hy₀ : N.symm y ∈ ball q ρ₀ :=
    Internal.symm_mem_ball_isometry N (ball_subset_ball (min_le_left _ _) hy)
  rw [N.image_eq_preimage_symm, mem_preimage]
  exact ⟨fun hS => (show y ∈ aboveGraph j γ ∩ ball (N q) ρ₁ by
      rw [← h₁]; exact ⟨(show N.symm y ∈ {w | 0 < G w} ∩ ball q ρ₀ by
        rw [← h₀]; exact ⟨hS, hy₀⟩).1, ball_subset_ball (min_le_right _ _) hy⟩).1,
    fun ha => (show N.symm y ∈ S ∩ ball q ρ₀ by
      rw [h₀]; exact ⟨(show y ∈ {y | 0 < G (N.symm y)} ∩ ball (N q) ρ₁ by
        rw [h₁]; exact ⟨ha, ball_subset_ball (min_le_right _ _) hy⟩).1, hy₀⟩).1⟩

/-- **Invariance of a `C¹` boundary under a linear equivalence.** If `Ω ⊆ ℝᵈ` has `C¹`
boundary, so does its image under every continuous linear equivalence of `ℝᵈ`. -/
theorem HasC1Boundary.image_linearEquiv {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : HasC1Boundary Ω) (A : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    HasC1Boundary (A '' Ω) := by
  intro x hx
  rw [← show A '' frontier Ω = frontier (A '' Ω) by simpa using A.toHomeomorph.image_frontier Ω]
    at hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨c, hc⟩ := hΩ x₀ hx₀
  obtain ⟨N, hN⟩ := exists_isometry_pos (fderiv_chartFn_ne_zero c A (A x₀)) c.dir
  obtain ⟨ρ₁, hρ₁, γ, hγ, hind, hgraph⟩ := exists_aboveGraph_of_fderiv_pos (j := c.dir)
    (H := chartFn c A ∘ N.symm) (p := N (A x₀))
    ((contDiff_chartFn c A).comp N.symm.contDiff)
    (by simp [chartFn, chartMap, c.graph_motion_eq_of_mem_frontier hc hx₀])
    (by rw [show chartFn c A ∘ N.symm = chartFn c A ∘
        N.symm.toContinuousLinearEquiv from rfl,
        N.symm.toContinuousLinearEquiv.comp_right_fderiv]
        change 0 < fderiv ℝ (chartFn c A) (N.symm (N (A x₀)))
          (N.symm (EuclideanSpace.single c.dir 1))
        rwa [N.symm_apply_apply])
  exact ⟨⟨N, c.dir, γ, min (imageRadius c A) ρ₁, lt_min (imageRadius_pos c A) hρ₁, hγ, hind⟩,
    image_isometry_inter_ball N (image_inter_ball c A hc) hgraph⟩

/-! ### `C¹` boundary in a finite-dimensional normed space -/

section Normed

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`C¹` boundary in a finite-dimensional real normed space.** The image under `toEuclidean`
has `C¹` boundary. By `hasC1BoundaryNormed_iff` any other continuous linear equivalence with
`ℝᵈ` gives the same notion. -/
def HasC1BoundaryNormed (Ω : Set E) : Prop :=
  HasC1Boundary (toEuclidean '' Ω : Set (EuclideanSpace ℝ (Fin (finrank ℝ E))))

/-- **Independence of the identification.** For every continuous linear equivalence
`L : E ≃L[ℝ] ℝᵈ`, `Ω` has `C¹` boundary exactly when `L '' Ω` does. -/
theorem hasC1BoundaryNormed_iff {Ω : Set E}
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E))) :
    HasC1BoundaryNormed Ω ↔ HasC1Boundary (L '' Ω) := by
  constructor
  · intro h
    simpa [image_image] using h.image_linearEquiv (toEuclidean.symm.trans L)
  · intro h
    simpa [HasC1BoundaryNormed, image_image] using h.image_linearEquiv (L.symm.trans toEuclidean)

/-- **Invariance on a normed space.** A continuous linear equivalence of `E` preserves `C¹`
boundaries. -/
theorem HasC1BoundaryNormed.image_linearEquiv {Ω : Set E} (h : HasC1BoundaryNormed Ω)
    (A : E ≃L[ℝ] E) : HasC1BoundaryNormed (A '' Ω) :=
  (hasC1BoundaryNormed_iff (A.symm.trans toEuclidean)).2
    (by simpa [HasC1BoundaryNormed, image_image] using h)

/-- **A half space has `C¹` boundary**, so `HasC1BoundaryNormed` holds on every
finite-dimensional real normed space. -/
theorem hasC1BoundaryNormed_halfSpace (j : Fin (finrank ℝ E)) :
    HasC1BoundaryNormed ((toEuclidean : E ≃L[ℝ] _) ⁻¹' halfSpace j) := by
  rw [HasC1BoundaryNormed, image_preimage_eq _ toEuclidean.surjective]
  exact hasC1Boundary_halfSpace j

end Normed

end EllipticPdes.Extension
