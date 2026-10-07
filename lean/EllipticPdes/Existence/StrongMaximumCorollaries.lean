/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.StrongMaximum

/-!
# Corollaries of Hopf's lemma and the strong maximum principle

The free-sign clauses of Hopf's lemma and of the strong maximum principle, in which the
zeroth-order coefficient has any sign and the extremal value is zero, follow from the
nonnegative clauses by replacing `c` with its positive part: on the set where the function is
nonpositive the change of coefficient lowers the operator. The avoidance principle, the
tangency corollary at a boundary point with an interior sphere, and uniqueness for the
Neumann problem up to a constant then follow.

The statements are made for the coordinate-free operator `nondivOperator` and then specialised
to Euclidean space with a coefficient matrix.

## Main declarations

* `EllipticPdes.Classical.hopf_lemma_of_zero`: Hopf's lemma with `c` of any sign and
  `u x₀ = 0`.
* `EllipticPdes.Classical.strong_maximum_principle_of_zero`: the strong principle at a zero
  maximum with `c` of any sign.
* `EllipticPdes.Classical.avoidance_principle`: two ordered functions with ordered images
  either agree or are strictly ordered.
* `EllipticPdes.Classical.eq_of_eq_of_fderiv_eq`: tangency at a boundary point with an
  interior sphere forces equality.
* `EllipticPdes.Classical.neumann_unique`: uniqueness up to a constant for the Neumann problem.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Lemma XI.4.3,
Theorem XI.4.5, Corollaries XI.4.6, XI.4.7 and XI.4.8 (pp. 100–103).
-/

@[expose] public section

open Set Filter Topology Metric InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Classical

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {U : Set E} {θ T B C : ℝ}

/-- The operator with the positive part of the zeroth-order coefficient is at most the operator
with the coefficient itself, on a nonpositive function. -/
theorem nondivOperator_posPart_le (A : E → E →L[ℝ] E) (b : E → E) (c : E → ℝ) {u : E → ℝ}
    {x : E} (hux : u x ≤ 0) :
    nondivOperator A b (fun y => max (c y) 0) u x ≤ nondivOperator A b c u x := by
  rw [nondivOperator_congr_zeroth A b c (fun y => max (c y) 0) u x]
  nlinarith [mul_nonneg (sub_nonneg.2 (le_max_left (c x) 0)) (neg_nonneg.mpr hux)]

/-- A function constant on a set and continuous on its closure is constant on the closure. -/
theorem eq_on_closure_of_eq_on {X : Type*} [TopologicalSpace X] {U : Set X} {w : X → ℝ}
    (hwc : ContinuousOn w (closure U)) {M : ℝ} (h : ∀ x ∈ U, w x = M) :
    ∀ x ∈ closure U, w x = M := fun _ hx =>
  ((hwc.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton |>.closure_subset_iff.mpr
    (fun y hy => ⟨subset_closure hy, h y hy⟩)) hx).2

namespace nondivOperator

/-- **Hopf's lemma at a zero boundary value** (Guo Lemma XI.4.3(iii)). With the zeroth-order
coefficient bounded in absolute value and of any sign, a subsolution strictly negative on the
ball, vanishing at a point `x₀` of the sphere and differentiable there, has positive derivative
at `x₀` in the outward radial direction. -/
theorem hopf_lemma_of_zero (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (huc : ContinuousOn u (closure U))
    (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0) {x₀ y : E} {r : ℝ} (hr : 0 < r)
    (hball : ball y r ⊆ U) (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hu0 : u x₀ = 0)
    (hdiff : DifferentiableAt ℝ u x₀) : 0 < fderiv ℝ u x₀ (x₀ - y) :=
  hopf_lemma hA hT hb (c := fun x => max (c x) 0) (C := C) (fun x _ => le_max_right _ _)
    (fun x hx => max_le ((le_abs_self _).trans (hc x hx)) ((abs_nonneg _).trans (hc x hx))) hu huc
    (fun x hx => (nondivOperator_posPart_le A b c (by linarith [hlt x hx])).trans (hsub x hx))
    hr hball hx₀ hlt (fun x _ => by rw [hu0, mul_zero]) hdiff

/-- **Strong maximum principle at a zero maximum** (Guo Theorem XI.4.5(iii)). With the
zeroth-order coefficient bounded in absolute value and of any sign, a subsolution on a connected
open set that attains the maximum zero at an interior point vanishes on the set. -/
theorem strong_maximum_principle_of_zero (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀) (hu0 : u x₀ = 0) :
    ∀ x ∈ U, u x = u x₀ :=
  strong_maximum_principle hU hUc hA hT hb (c := fun x => max (c x) 0) (C := C)
    (fun x _ => le_max_right _ _)
    (fun x hx => max_le ((le_abs_self _).trans (hc x hx)) ((abs_nonneg _).trans (hc x hx))) hu
    (fun x hx => (nondivOperator_posPart_le A b c (by linarith [hmax x hx])).trans (hsub x hx))
    hx₀ hmax (fun x _ => by rw [hu0, mul_zero])

/-- **Avoidance principle** (Guo Corollary XI.4.6). On a connected open set, with the
zeroth-order coefficient bounded in absolute value, two functions with `L u ≤ L v` and `u ≤ v`
either agree everywhere or satisfy `u < v` everywhere. -/
theorem avoidance_principle (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x)
    (hle : ∀ x ∈ U, u x ≤ v x) : (∀ x ∈ U, u x = v x) ∨ (∀ x ∈ U, u x < v x) := by
  by_cases h : ∃ x₀ ∈ U, u x₀ = v x₀
  · obtain ⟨x₀, hx₀, hx₀eq⟩ := h
    left
    have hw : ∀ x ∈ U, nondivOperator A b c (fun y => u y - v y) x ≤ 0 := fun x hx => by
      rw [nondivOperator_sub A b c (hu.contDiffAt (hU.mem_nhds hx))
        (hv.contDiffAt (hU.mem_nhds hx))]
      linarith [hL x hx]
    have hcst := strong_maximum_principle_of_zero hU hUc hA hT hb hc (hu.sub hv) hw hx₀
      (fun x hx => by linarith [hle x hx, hle x₀ hx₀]) (by linarith)
    intro x hx
    linarith [hcst x hx]
  · right
    intro x hx
    exact (hle x hx).lt_of_ne fun h1 => h ⟨x, hx, h1⟩

/-- **Tangency at a boundary point forces equality** (Guo Corollary XI.4.7, with the interior
sphere condition at the point in place of a `C²` boundary). On a connected open set, two
functions with `L u ≤ L v`, `u ≤ v` on the set, equal with equal derivatives at a point `x₀`
of the frontier that is on the sphere of a ball inside the set, agree on the set. -/
theorem eq_of_eq_of_fderiv_eq (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x)
    (hle : ∀ x ∈ U, u x ≤ v x) {x₀ y : E} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (heq : u x₀ = v x₀) (hfd : fderiv ℝ u x₀ = fderiv ℝ v x₀)
    (hud : DifferentiableAt ℝ u x₀) (hvd : DifferentiableAt ℝ v x₀) : ∀ x ∈ U, u x = v x := by
  rcases avoidance_principle hU hUc hA hT hb hc hu hv hL hle with h | h
  · exact h
  · exfalso
    have hw : ∀ x ∈ U, nondivOperator A b c (fun y => u y - v y) x ≤ 0 := fun x hx => by
      rw [nondivOperator_sub A b c (hu.contDiffAt (hU.mem_nhds hx))
        (hv.contDiffAt (hU.mem_nhds hx))]
      linarith [hL x hx]
    have hhopf := hopf_lemma_of_zero hA hT hb hc (hu.sub hv) (huc.sub hvc) hw hr hball hx₀
      (fun x hx => by linarith [h x hx]) (by linarith) (hud.sub hvd)
    have hfw : fderiv ℝ (fun y => u y - v y) x₀ = 0 := by
      rw [fderiv_fun_sub hud hvd, hfd, sub_self]
    rw [hfw] at hhopf
    simp at hhopf

/-- A solution with nonnegative maximum over the closure and zero normal derivative along an
interior sphere at every frontier point is constant on the closure. -/
theorem eq_const_of_neumann_aux (hU : IsOpen U) (hUc : IsPreconnected U)
    (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x)
    (hcC : ∀ x ∈ U, c x ≤ C) {w : E → ℝ} (hw : ContDiffOn ℝ 2 w U)
    (hwc : ContinuousOn w (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c w x ≤ 0)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ w y ∧ ∃ z r, 0 < r ∧ ball z r ⊆ U ∧
      dist y z = r ∧ fderiv ℝ w y (y - z) = 0)
    {p : E} (hp : p ∈ closure U) (hpmax : ∀ x ∈ closure U, w x ≤ w p) (hp0 : 0 ≤ w p) :
    ∀ x ∈ closure U, w x = w p := by
  -- an interior maximum point gives constancy
  have hint : ∀ x₀ ∈ U, w x₀ = w p → ∀ x ∈ closure U, w x = w p := fun x₀ hx₀ hx₀eq =>
    eq_on_closure_of_eq_on hwc fun x hx => by
      rw [strong_maximum_principle hU hUc hA hT hb hc0 hcC hw hsub hx₀
        (fun x hx => by rw [hx₀eq]; exact hpmax x (subset_closure hx))
        (fun x hx => by rw [hx₀eq]; exact mul_nonneg (hc0 x hx) hp0) x hx, hx₀eq]
  by_cases hex : ∃ x₀ ∈ U, w x₀ = w p
  · obtain ⟨x₀, hx₀, hx₀eq⟩ := hex
    exact hint x₀ hx₀ hx₀eq
  · by_cases hpU : p ∈ U
    · exact hint p hpU rfl
    · exfalso
      have hlt : ∀ x ∈ U, w x < w p := fun x hx =>
        lt_of_le_of_ne (hpmax x (subset_closure hx)) fun h => hex ⟨x, hx, h⟩
      obtain ⟨hdiff, z, r, hr, hball, hdist, hfz⟩ :=
        hν p (by rw [hU.frontier_eq]; exact ⟨hp, hpU⟩)
      have hhopf := hopf_lemma hA hT hb hc0 hcC hw hwc hsub hr hball hdist hlt
        (fun x hx => mul_nonneg (hc0 x hx) hp0) hdiff
      rw [hfz] at hhopf
      exact lt_irrefl _ hhopf

/-- **Uniqueness for the Neumann problem** (Guo Corollary XI.4.8). On a bounded connected open
set with an interior sphere at every frontier point, with `c ≥ 0` bounded, two functions with
the same image under `L`, differentiable at every frontier point and with the same derivative
there along the radius of an interior sphere, differ by a constant on the closure. -/
theorem neumann_unique (hU : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ) (hT : ∀ x ∈ U, LinearMap.trace ℝ E
      (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B) (hc0 : ∀ x ∈ U, 0 ≤ c x)
    (hcC : ∀ x ∈ U, c x ≤ C) {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x = nondivOperator A b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∃ M : ℝ, ∀ x ∈ closure U, u x = v x + M := by
  set w : E → ℝ := fun y => u y - v y with hwdef
  have hw : ContDiffOn ℝ 2 w U := hu.sub hv
  have hwc : ContinuousOn w (closure U) := huc.sub hvc
  have hsol : ∀ x ∈ U, nondivOperator A b c w x = 0 := fun x hx => by
    rw [hwdef, nondivOperator_sub A b c (hu.contDiffAt (hU.mem_nhds hx))
      (hv.contDiffAt (hU.mem_nhds hx)), hL x hx, sub_self]
  have hwν : ∀ y ∈ frontier U, DifferentiableAt ℝ w y ∧ ∃ z r, 0 < r ∧ ball z r ⊆ U ∧
      dist y z = r ∧ fderiv ℝ w y (y - z) = 0 := fun y hy => by
    obtain ⟨hud, hvd, z, r, hr, hball, hdist, hfd⟩ := hν y hy
    refine ⟨hud.sub hvd, z, r, hr, hball, hdist, ?_⟩
    rw [hwdef, fderiv_fun_sub hud hvd, sub_apply, hfd, sub_self]
  have hcl : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨p, hp, hpmax⟩ := hcl.exists_isMaxOn hUne.closure hwc
  obtain ⟨q, hq, hqmin⟩ := hcl.exists_isMinOn hUne.closure hwc
  rcases le_or_gt 0 (w p) with hp0 | hp0
  · refine ⟨u p - v p, fun x hx => ?_⟩
    have := eq_const_of_neumann_aux hU hUc hA hT hb hc0 hcC hw hwc
      (fun x hx => (hsol x hx).le) hwν hp (fun x hx => hpmax hx) hp0 x hx
    simp only [hwdef] at this
    linarith
  · -- the negative of `w` has nonnegative maximum at `q`
    have hnν : ∀ y ∈ frontier U, DifferentiableAt ℝ (fun y => -w y) y ∧ ∃ z r, 0 < r ∧
        ball z r ⊆ U ∧ dist y z = r ∧ fderiv ℝ (fun y => -w y) y (y - z) = 0 := fun y hy => by
      obtain ⟨hd', z, r, hr, hball, hdist, hfz⟩ := hwν y hy
      refine ⟨hd'.neg, z, r, hr, hball, hdist, ?_⟩
      rw [fderiv_fun_neg, neg_apply, hfz, neg_zero]
    refine ⟨u q - v q, fun x hx => ?_⟩
    have := eq_const_of_neumann_aux hU hUc hA hT hb hc0 hcC hw.neg hwc.neg
      (fun x hx => by
        rw [nondivOperator_neg A b c (hw.contDiffAt (hU.mem_nhds hx)), hsol x hx, neg_zero])
      hnν hq (fun x hx => by
        have := (show w q ≤ w x from hqmin hx)
        change -w x ≤ -w q
        linarith)
      (by
        have := (show w q ≤ w p from hpmax hq)
        change 0 ≤ -w q
        linarith) x hx
    simp only [hwdef] at this
    linarith

/-- **Uniqueness for the Neumann problem with a nonzero zeroth-order coefficient** (Guo Remark
XI.4.9). When `c` is nonzero somewhere on the set, the constant is zero. -/
theorem neumann_unique_of_exists_pos (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) (hA : IsUniformlyElliptic A U θ)
    (hT : ∀ x ∈ U, LinearMap.trace ℝ E (A x : E →ₗ[ℝ] E) ≤ T) (hb : ∀ x ∈ U, ‖b x‖ ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C) (hcpos : ∃ x ∈ U, c x ≠ 0)
    {u v : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOperator A b c u x = nondivOperator A b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∀ x ∈ closure U, u x = v x := by
  obtain ⟨M, hM⟩ := neumann_unique hU hUc hUb hUne hA hT hb hc0 hcC hu hv huc hvc hL hν
  obtain ⟨x₁, hx₁, hc₁⟩ := hcpos
  -- near `x₁` the difference `u - v` is the constant `M`, so `L` of it is `c M`
  have hwM : (fun y => u y - v y) =ᶠ[𝓝 x₁] fun _ => M :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx₁) fun x hx => by
      linarith [hM x (subset_closure hx)]
  have hL' := nondivOperator_congr_of_eventuallyEq A b c hwM
  rw [nondivOperator_sub A b c (hu.contDiffAt (hU.mem_nhds hx₁)) (hv.contDiffAt (hU.mem_nhds hx₁)),
    hL x₁ hx₁, sub_self, nondivOperator_const] at hL'
  have hM0 : M = 0 := (mul_eq_zero.mp hL'.symm).resolve_left hc₁
  intro x hx
  simpa [hM0] using hM x hx

end nondivOperator

end General


/-! ### Euclidean space with a coefficient matrix -/

variable {d : ℕ}

/-- The Euclidean hypotheses on the coefficients give the coordinate-free ones. -/
theorem euclid_hyps {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ}
    {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ} {θ A B : ℝ} (hθ : 0 < θ)
    (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) :
    IsUniformlyElliptic (fun x => matrixCLM (a x)) U θ ∧
      (∀ x ∈ U, LinearMap.trace ℝ (EuclideanSpace ℝ (Fin d)) (matrixCLM (a x) : _ →ₗ[ℝ] _)
        ≤ d * A) ∧ ∀ x ∈ U, ‖(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d))‖ ≤ d * B :=
  ⟨isUniformlyElliptic_matrixCLM hθ hsymm hell, fun x hx => trace_matrixCLM_le (ha x hx),
    fun x hx => norm_toLp_le (hb x hx)⟩

/-- **Hopf's lemma at a zero boundary value** (Guo Lemma XI.4.3(iii)). With the zeroth-order
coefficient bounded in absolute value and of any sign, a subsolution strictly negative on the
ball, vanishing at a point `x₀` of the sphere and differentiable there, has positive derivative
at `x₀` in the outward radial direction. -/
theorem hopf_lemma_of_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (hlt : ∀ x ∈ U, u x < u x₀) (hu0 : u x₀ = 0)
    (hdiff : DifferentiableAt ℝ u x₀) :
    0 < fderiv ℝ u x₀ (x₀ - y) := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  have hopen := isOpen_ball (x := y) (ε := r)
  exact nondivOperator.hopf_lemma_of_zero (U := ball y r) (hA.mono hball)
    (fun x hx => hT x (hball hx)) (fun x hx => hb' x (hball hx)) (fun x hx => hc x (hball hx))
    (hu.mono hball) (huc.mono (closure_mono hball))
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hopen (hu.mono hball) hx]; exact hsub x (hball hx))
    hr subset_rfl hx₀ (fun x hx => hlt x (hball hx)) hu0 hdiff

/-- **Strong maximum principle at a zero maximum** (Guo Theorem XI.4.5(iii)). With the
zeroth-order coefficient bounded in absolute value and of any sign, a subsolution on a connected
open set that attains the maximum zero at an interior point vanishes on the set. -/
theorem strong_maximum_principle_of_zero (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ 0)
    {x₀ : EuclideanSpace ℝ (Fin d)} (hx₀ : x₀ ∈ U) (hmax : ∀ x ∈ U, u x ≤ u x₀)
    (hu0 : u x₀ = 0) : ∀ x ∈ U, u x = u x₀ := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  exact nondivOperator.strong_maximum_principle_of_zero hU hUc hA hT hb' hc hu
    (fun x hx => by rw [← nondivOp_eq_of_contDiffOn hU hu hx]; exact hsub x hx) hx₀ hmax hu0

/-- **Avoidance principle** (Guo Corollary XI.4.6). On a connected open set, with the
zeroth-order coefficient bounded in absolute value, two functions with `L u ≤ L v` and `u ≤ v`
either agree everywhere or satisfy `u < v` everywhere. -/
theorem avoidance_principle (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x) (hle : ∀ x ∈ U, u x ≤ v x) :
    (∀ x ∈ U, u x = v x) ∨ (∀ x ∈ U, u x < v x) := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  exact nondivOperator.avoidance_principle hU hUc hA hT hb' hc hu hv
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hle

/-- **Tangency at a boundary point forces equality** (Guo Corollary XI.4.7, with the interior
sphere condition at the point in place of a `C²` boundary). On a connected open set, two
functions with `L u ≤ L v`, `u ≤ v` on the set, equal with equal derivatives at a point `x₀`
of the frontier that is on the sphere of a ball inside the set, agree on the set. -/
theorem eq_of_eq_of_fderiv_eq (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {θ A B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} (hc : ∀ x ∈ U, |c x| ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x ≤ nondivOp a b c v x) (hle : ∀ x ∈ U, u x ≤ v x)
    {x₀ y : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ U)
    (hx₀ : dist x₀ y = r) (heq : u x₀ = v x₀) (hfd : fderiv ℝ u x₀ = fderiv ℝ v x₀)
    (hud : DifferentiableAt ℝ u x₀) (hvd : DifferentiableAt ℝ v x₀) :
    ∀ x ∈ U, u x = v x := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  exact nondivOperator.eq_of_eq_of_fderiv_eq hU hUc hA hT hb' hc hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hle hr hball hx₀ heq hfd hud hvd

/-- **Uniqueness for the Neumann problem** (Guo Corollary XI.4.8). On a bounded connected open
set with an interior sphere at every frontier point, with `c ≥ 0` bounded, two functions with
the same image under `L`, differentiable at every frontier point and with the same derivative
there along the radius of an interior sphere, differ by a constant on the closure. -/
theorem neumann_unique (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∃ M : ℝ, ∀ x ∈ closure U, u x = v x + M := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  exact nondivOperator.neumann_unique hU hUc hUb hUne hA hT hb' hc0 hcC hu hv huc hvc
    (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hν

/-- **Uniqueness for the Neumann problem with a nonzero zeroth-order coefficient** (Guo Remark
XI.4.9). When `c` is positive somewhere on the set, the constant is zero. -/
theorem neumann_unique_of_exists_pos (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ A B C : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (ha : ∀ x ∈ U, ∀ i j, |a x i j| ≤ A) (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B)
    (hc0 : ∀ x ∈ U, 0 ≤ c x) (hcC : ∀ x ∈ U, c x ≤ C) (hcpos : ∃ x ∈ U, c x ≠ 0)
    {u v : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hL : ∀ x ∈ U, nondivOp a b c u x = nondivOp a b c v x)
    (hν : ∀ y ∈ frontier U, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ v y ∧
      ∃ z r, 0 < r ∧ ball z r ⊆ U ∧ dist y z = r ∧
        fderiv ℝ u y (y - z) = fderiv ℝ v y (y - z)) :
    ∀ x ∈ closure U, u x = v x := by
  have _ := hd
  obtain ⟨hA, hT, hb'⟩ := euclid_hyps hθ hsymm hell ha hb
  exact nondivOperator.neumann_unique_of_exists_pos hU hUc hUb hUne hA hT hb' hc0 hcC hcpos hu hv
    huc hvc (fun x hx => by
      rw [← nondivOp_eq_of_contDiffOn hU hu hx, ← nondivOp_eq_of_contDiffOn hU hv hx]
      exact hL x hx) hν

end EllipticPdes.Classical
