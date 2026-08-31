/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.DifferentiatedEquation

/-!
# Dividing a `C¹` weight out of a weak derivative

Step 5 of the proof of Evans, *Partial Differential Equations* (2nd ed.), §6.3.2,
Theorem 4 (*Boundary `H²` regularity*) rearranges the nondivergence form (52) of `Lu = f`
into (53), isolating `a^{nn} u_{x_n x_n}`, and then divides by `a^{nn} ≥ θ > 0` (equation
(54), ellipticity at `ξ = e_n`) to reach the pointwise bound (55) on `u_{x_n x_n}`.

At the point that step is invoked only the tangential second derivatives are known to be
`L²`, so (53) is available as a statement about the weak derivative of the *product*
`a^{nn} u_{x_n}`, and the passage to `u_{x_n} ∈ H¹` costs a division. This file supplies
that division: the inverse of the weighted product rule
`EllipticPdes.Regularity.HasWeakDerivOn.mul_contDiff_left`.

The mathematical content is one line, `v = a⁻¹ · (a · v)`, and the whole difficulty sits in the
hypotheses on `a`. A bounded measurable `a` bounded away from zero falls short, since
differentiating `a⁻¹` costs a derivative of `a`. What the argument needs is

* `a ∈ C¹`, so that `a⁻¹` is `C¹` wherever `a` does not vanish;
* `a ≥ θ > 0` almost everywhere, which continuity of `a` upgrades to an everywhere bound
  (`le_of_ae_le_of_continuous`), and which then bounds `a⁻¹` by `θ⁻¹`;
* `∂_ℓ a` bounded almost everywhere, so that `∂_ℓ(a⁻¹) = -(∂_ℓ a)/a²` is a bounded weight
  and the resulting derivative lands in `L²`.

The project's `IsC1Coeff` mixin supplies the first and third of these for a coefficient
matrix, and `EllipticCoeff.lam_le_diag` below supplies the second from ellipticity at
`ξ = e_k`, which is Evans (54).

## Main declarations

* `le_of_ae_le_of_continuous`: an almost-everywhere lower bound on a continuous function
  holds everywhere, the measure having full support.
* `EllipticPdes.Sobolev.EllipticCoeff.lam_le_diag`: Evans (54), ellipticity at `ξ = e_k`.
* `HasWeakDerivOn.of_mul_contDiff_left`: the division itself.
* `exists_hasWeakDerivOn_of_mul_contDiff_left`: the same with the quotient class built and
  estimated, `‖∂_ℓ v‖ ≤ θ⁻¹‖∂_ℓ(a·v)‖ + (M/θ)‖v‖`, which is Evans (55).
* `exists_hasWeakDerivOn_of_mul_diag`: the packaged form for a `C¹` elliptic bundle, with
  the diagonal entry `a_{kk}` as the weight and ellipticity discharging the lower bound.
-/

open MeasureTheory
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Everywhere bound from an almost-everywhere bound -/

/-- **A continuous function bounded below almost everywhere is bounded below everywhere.**
The set where the bound holds is closed, and it is dense because its complement is null and
`volume` charges every nonempty open set, so it is the whole space. This is what turns the
almost-everywhere ellipticity of `EllipticCoeff` into the everywhere positivity that
`ContDiff.inv` demands. -/
theorem le_of_ae_le_of_continuous {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : Continuous a)
    {θ : ℝ} (h : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), θ ≤ a x)
    (x : EuclideanSpace ℝ (Fin d)) : θ ≤ a x := by
  have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin d) | θ ≤ a y} :=
    isClosed_le continuous_const ha
  have hdense : Dense {y : EuclideanSpace ℝ (Fin d) | θ ≤ a y} :=
    MeasureTheory.Measure.dense_of_ae h
  have huniv : {y : EuclideanSpace ℝ (Fin d) | θ ≤ a y} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  exact Set.eq_univ_iff_forall.mp huniv x

end EllipticPdes.Regularity

namespace EllipticPdes.Sobolev.EllipticCoeff

open MeasureTheory

variable {d : ℕ}

/-- **Ellipticity on the diagonal (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.2, Theorem 4, proof step 5, equation (54)).** Testing uniform ellipticity against
`ξ = e_k` leaves the single diagonal entry `a_{kk}`, so `a_{kk}(x) ≥ lam > 0` almost
everywhere. Evans states this at `k = n` to divide by `a^{nn}` in (53). -/
theorem lam_le_diag (A : EllipticCoeff d) (k : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), A.lam ≤ A.a x k k := by
  filter_upwards [A.elliptic] with x hx
  have h := hx (fun i => if i = k then (1 : ℝ) else 0)
  simpa using h

end EllipticPdes.Sobolev.EllipticCoeff

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Reciprocal weight -/

/-- The reciprocal of a `C¹` function bounded below by `θ > 0` is `C¹`. -/
private theorem contDiff_inv_of_le {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {θ : ℝ} (hθ : 0 < θ) (hbdd : ∀ x, θ ≤ a x) : ContDiff ℝ 1 (fun x => (a x)⁻¹) :=
  ha.inv fun x => ne_of_gt (lt_of_lt_of_le hθ (hbdd x))

/-- The partial derivative of a reciprocal: `∂_ℓ (a⁻¹) = -(a²)⁻¹ ∂_ℓ a`. -/
private theorem partialD_inv {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    (hne : ∀ x, a x ≠ 0) (ℓ : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD ℓ (fun y => (a y)⁻¹) x = -(a x ^ 2)⁻¹ * partialD ℓ a x := by
  have hfd : HasFDerivAt (fun y => (a y)⁻¹) ((-(a x ^ 2)⁻¹) • fderiv ℝ a x) x :=
    (hasDerivAt_inv (hne x)).comp_hasFDerivAt x (ha.differentiable_one x).hasFDerivAt
  simp only [partialD, hfd.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### Dividing the weight out -/

/-- **Weak-derivative division by a `C¹` weight bounded away from zero.** If `a · v` has weak
`ℓ`-derivative `dav` on `V`, and `a` is `C¹` with `a ≥ θ > 0` almost everywhere and
`∂_ℓ a` bounded almost everywhere, then `v` itself has weak `ℓ`-derivative
`(dav - (∂_ℓ a) · v) / a` on `V`.

This is the inverse of `HasWeakDerivOn.mul_contDiff_left`, and is what step 5 of the proof
of Evans, *Partial Differential Equations* (2nd ed.), §6.3.2, Theorem 4 (*Boundary `H²`
regularity*) needs to pass from the rearranged equation (53), which controls the weak
derivative of the product `a^{nn} u_{x_n}`, to `u_{x_n} ∈ H¹` and hence to the pointwise
bound (55). Proved by writing `v = a⁻¹ · (a · v)` and applying the product rule at the
weight `a⁻¹`, whose `C¹` regularity is where the hypotheses on `a` are spent. -/
theorem HasWeakDerivOn.of_mul_contDiff_left {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) (ℓ : Fin d)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {θ M : ℝ} (hθ : 0 < θ)
    (haθ : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), θ ≤ a x)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |partialD ℓ a x| ≤ M)
    {v av dav v' : Lp ℝ 2 (volume.restrict V)}
    (hav : av =ᵐ[volume.restrict V] fun x => a x * (v x : ℝ))
    (hd : HasWeakDerivOn V ℓ av dav)
    (hv' : v' =ᵐ[volume.restrict V]
      fun x => ((dav x : ℝ) - partialD ℓ a x * (v x : ℝ)) / a x) :
    HasWeakDerivOn V ℓ v v' := by
  have hbdd : ∀ x, θ ≤ a x := le_of_ae_le_of_continuous ha.continuous haθ
  have hpos : ∀ x, 0 < a x := fun x => lt_of_lt_of_le hθ (hbdd x)
  have hne : ∀ x, a x ≠ 0 := fun x => ne_of_gt (hpos x)
  have hbC1 : ContDiff ℝ 1 (fun x => (a x)⁻¹) := contDiff_inv_of_le ha hθ hbdd
  -- the reciprocal is bounded by `θ⁻¹`
  have hbM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |(a x)⁻¹| ≤ θ⁻¹ := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [abs_of_pos (inv_pos.mpr (hpos x))]
    exact inv_anti₀ hθ (hbdd x)
  -- its derivative is bounded by `M / θ²`
  have hdbM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      |partialD ℓ (fun y => (a y)⁻¹) x| ≤ M / θ ^ 2 := by
    filter_upwards [hdaM] with x hx
    rw [partialD_inv ha hne ℓ x, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr (pow_pos (hpos x) 2))]
    rw [div_eq_inv_mul]
    refine mul_le_mul ?_ hx (abs_nonneg _) (by positivity)
    exact inv_anti₀ (pow_pos hθ 2) (pow_le_pow_left₀ hθ.le (hbdd x) 2)
  -- `v = a⁻¹ · (a · v)` and `v' = (∂_ℓ a⁻¹) · (a · v) + a⁻¹ · dav`
  have hvrep : v =ᵐ[volume.restrict V] fun x => (a x)⁻¹ * (av x : ℝ) := by
    filter_upwards [hav] with x hx
    rw [hx, ← mul_assoc, inv_mul_cancel₀ (hne x), one_mul]
  have hv'rep : v' =ᵐ[volume.restrict V]
      fun x => partialD ℓ (fun y => (a y)⁻¹) x * (av x : ℝ) + (a x)⁻¹ * (dav x : ℝ) := by
    filter_upwards [hv', hav] with x hx hax
    have h0 : a x ≠ 0 := hne x
    rw [hx, hax, partialD_inv ha hne ℓ x]
    field_simp
    ring
  exact HasWeakDerivOn.mul_contDiff_left hVm ℓ hd hbC1 hbM hdbM v hvrep v' hv'rep

/-- **Existence and estimate of the quotient class.** Under the hypotheses of
`HasWeakDerivOn.of_mul_contDiff_left`, the weak `ℓ`-derivative of `v` is an `L²(V)` class
with
`‖∂_ℓ v‖ ≤ θ⁻¹ ‖∂_ℓ(a·v)‖ + (M/θ) ‖v‖`.
That estimate is the `L²` form of Evans, *Partial Differential Equations* (2nd ed.),
§6.3.2, Theorem 4 (*Boundary `H²` regularity*), proof step 5, equation (55), where the
pointwise bound on `u_{x_n x_n}` is obtained by dividing (53) by `a^{nn} ≥ θ`. -/
theorem exists_hasWeakDerivOn_of_mul_contDiff_left {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) (ℓ : Fin d)
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {θ M : ℝ} (hθ : 0 < θ)
    (haθ : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), θ ≤ a x)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |partialD ℓ a x| ≤ M)
    {v av dav : Lp ℝ 2 (volume.restrict V)}
    (hav : av =ᵐ[volume.restrict V] fun x => a x * (v x : ℝ))
    (hd : HasWeakDerivOn V ℓ av dav) :
    ∃ v' : Lp ℝ 2 (volume.restrict V),
      HasWeakDerivOn V ℓ v v'
        ∧ v' =ᵐ[volume.restrict V]
            (fun x => ((dav x : ℝ) - partialD ℓ a x * (v x : ℝ)) / a x)
        ∧ ‖v'‖ ≤ θ⁻¹ * ‖dav‖ + M / θ * ‖v‖ := by
  have hbdd : ∀ x, θ ≤ a x := le_of_ae_le_of_continuous ha.continuous haθ
  have hpos : ∀ x, 0 < a x := fun x => lt_of_lt_of_le hθ (hbdd x)
  have hdacont : Continuous (partialD ℓ a) :=
    (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hinvle : ∀ x, (a x)⁻¹ ≤ θ⁻¹ := fun x => inv_anti₀ hθ (hbdd x)
  -- the two bounded weights `a⁻¹` and `-(∂_ℓ a)/a`
  have hbmeas : Measurable (fun x => (a x)⁻¹) :=
    (ha.continuous.inv₀ fun x => (hpos x).ne').measurable
  have hcmeas : Measurable (fun x => -(partialD ℓ a x / a x)) :=
    ((hdacont.div ha.continuous fun x => (hpos x).ne').neg).measurable
  have hbM : ∀ᵐ x ∂(volume.restrict V), |(a x)⁻¹| ≤ θ⁻¹ := by
    refine Filter.Eventually.of_forall fun x => ?_
    rw [abs_of_pos (inv_pos.mpr (hpos x))]
    exact hinvle x
  have hcM : ∀ᵐ x ∂(volume.restrict V), |-(partialD ℓ a x / a x)| ≤ M / θ := by
    filter_upwards [ae_restrict_of_ae hdaM] with x hx
    rw [abs_neg, abs_div, abs_of_pos (hpos x), div_eq_mul_inv, div_eq_mul_inv]
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) hx
    exact mul_le_mul hx (hinvle x) (inv_pos.mpr (hpos x)).le hM0
  have hrep : (mulCoeffL hbmeas hbM dav + mulCoeffL hcmeas hcM v : Lp ℝ 2 (volume.restrict V))
      =ᵐ[volume.restrict V]
        fun x => ((dav x : ℝ) - partialD ℓ a x * (v x : ℝ)) / a x := by
    filter_upwards [Lp.coeFn_add (mulCoeffL hbmeas hbM dav) (mulCoeffL hcmeas hcM v),
      mulCoeffL_coeFn hbmeas hbM dav, mulCoeffL_coeFn hcmeas hcM v] with x h1 h2 h3
    have h0 : a x ≠ 0 := (hpos x).ne'
    rw [h1, Pi.add_apply, h2, h3]
    field_simp
    ring
  refine ⟨mulCoeffL hbmeas hbM dav + mulCoeffL hcmeas hcM v,
    HasWeakDerivOn.of_mul_contDiff_left hVm ℓ ha hθ haθ hdaM hav hd hrep, hrep, ?_⟩
  · refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact norm_mulCoeffL_le hbmeas hbM dav
    · exact norm_mulCoeffL_le hcmeas hcM v

/-- **Packaged form for a `C¹` elliptic bundle.** With `a := a_{kk}` the `k`-th diagonal
coefficient entry, ellipticity supplies the lower bound `a_{kk} ≥ lam > 0` (Evans (54)) and
`IsC1Coeff` supplies both the `C¹` regularity and the gradient bound `A₁`, so the division runs
on the data the boundary programme already has. At `ℓ = k = n` this is exactly the passage from
the rearranged equation (53) to `u_{x_n} ∈ H¹` in step 5 of the proof of Evans, *Partial
Differential Equations* (2nd ed.), §6.3.2, Theorem 4 (*Boundary `H²` regularity*). -/
theorem exists_hasWeakDerivOn_of_mul_diag {V : Set (EuclideanSpace ℝ (Fin d))}
    (hVm : MeasurableSet V) (A : EllipticCoeff d) (hA : IsC1Coeff A) (ℓ k : Fin d)
    {v av dav : Lp ℝ 2 (volume.restrict V)}
    (hav : av =ᵐ[volume.restrict V] fun x => A.a x k k * (v x : ℝ))
    (hd : HasWeakDerivOn V ℓ av dav) :
    ∃ v' : Lp ℝ 2 (volume.restrict V),
      HasWeakDerivOn V ℓ v v'
        ∧ v' =ᵐ[volume.restrict V]
            (fun x => ((dav x : ℝ) - partialD ℓ (fun y => A.a y k k) x * (v x : ℝ))
              / A.a x k k)
        ∧ ‖v'‖ ≤ A.lam⁻¹ * ‖dav‖ + hA.A1 / A.lam * ‖v‖ := by
  refine exists_hasWeakDerivOn_of_mul_contDiff_left hVm ℓ (hA.contDiff k k) A.lam_pos
    (A.lam_le_diag k) (Filter.Eventually.of_forall fun x => ?_) hav hd
  calc |partialD ℓ (fun y => A.a y k k) x|
      = ‖(fderiv ℝ (fun y => A.a y k k) x) (EuclideanSpace.single ℓ (1 : ℝ))‖ := by
        rw [partialD, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (fun y => A.a y k k) x‖ * ‖EuclideanSpace.single ℓ (1 : ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ hA.A1 := by
        rw [show ‖EuclideanSpace.single ℓ (1 : ℝ)‖ = 1 by simp, mul_one]
        exact hA.grad_bdd k k x

end EllipticPdes.Regularity
