/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Boundary.HalfBall
import EllipticPdes.Regularity.RestrictedDiffQuotient
import EllipticPdes.Regularity.CutoffTower

/-!
# Tangential difference quotients on the half-ball

The boundary `H²` estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.2,
Theorem 4, *Boundary `H²` regularity*) runs the difference-quotient method on the half-ball
`U = B⁰(0, 1) ∩ ℝⁿ₊` in directions parallel to the flat part of `∂U` only. This file supplies
that layer: the tangential difference quotient itself, the cutoff Evans selects in proof
step 1, and the support calculus that makes the cutoff of a tangential difference quotient of
a test function a test function again.

Two things separate this from the interior layer (`Regularity/RestrictedDiffQuotient.lean`,
`Regularity/RestrictedDiffQuotientMem.lean`), which the whole file otherwise mirrors.

* **Reach of the cutoff to the flat boundary.** Evans' `ζ` satisfies `ζ ≡ 1` on `B(0, 1/2)` and
  `ζ ≡ 0` off `B(0, 1)`, so it vanishes near the curved part of `∂U` and is unconstrained on
  the flat part `{xₙ = 0}`. It is therefore a test function on the *ball* `B(0, r)` rather
  than on the half-ball, and `mulTest` / `cutoffMul`
  (`EllipticPdes.Regularity.Caccioppoli`), whose cutoff is a test function on the domain
  itself, do not accept it. `mulCutoff`, `mulCutoffPartial` and `cutoffMulOn` below decouple
  the two: the cutoff is a test function on an ambient set `Ω'`, the operators act on
  `L²(Ω)` for an unrelated `Ω`.
* **Only tangential directions are admissible.** A translation in the normal direction can
  carry a point of the half-ball across the flat boundary, a tangential one cannot
  (`tangential_add_hshift_mem_halfBall`, `Regularity/Boundary/HalfBall.lean`). The support
  calculus here turns that into the statement that the tangential difference quotient of a
  test function on the half-ball is still supported in the open half-space `{x | 0 < x 0}`,
  with no smallness condition on the step `h`.

Coordinate `0` is Evans' normal direction `xₙ` and tangential directions are `k.succ` for
`k : Fin d`, matching `Regularity/Boundary/HalfBall.lean`.

## Main declarations

* `mulCutoff`, `mulCutoffPartial`, `cutoffMulOn`: the cutoff multipliers for a cutoff
  supported in an ambient set, generalising `mulTest`, `mulTestPartial` and `cutoffMul`.
* `tangDiffQuotD`, `tangDiffQuotG`: the tangential difference quotient on `L²` of the
  half-ball and on its graph space.
* `exists_tangentialCutoff`: Evans' cutoff, a test function on `B(0, r)` valued in `[0, 1]`
  and equal to `1` on a neighbourhood of `closedBall 0 (r / 2)`, hence on the closure of the
  smaller half-ball (`eqOn_one_closure_halfBall`).
* `isTestFn_tangentialCutoff_diffQuotFn`: the cutoff of a tangential difference quotient of a
  test function on the half-ball is a test function on the half-ball.
-/

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

/-! ### Cutoff multipliers for a cutoff supported in an ambient set -/

section Multipliers

variable {n : ℕ} {Ω Ω' : Set (EuclideanSpace ℝ (Fin n))} {η : EuclideanSpace ℝ (Fin n) → ℝ}

/-- **Multiplication by an ambiently supported cutoff** on `L²(Ω)`. The cutoff `η` is a test
function on some set `Ω'` unrelated to `Ω`, so its support may meet `∂Ω`; only smoothness and
compact support of `η` are used, exactly as in `mulTest`
(`EllipticPdes.Regularity.mulTest`), which is the case `Ω' = Ω`. The boundary `H²` estimate
needs this because Evans' cutoff vanishes near the curved part of `∂U` alone (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 1). -/
def mulCutoff (Ω : Set (EuclideanSpace ℝ (Fin n))) (hη : IsTestFn Ω' η) :
    L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL hη.continuous.measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound hη).choose_spec)

/-- **Multiplication by the partial `∂ᵢη` of an ambiently supported cutoff** on `L²(Ω)`, the
companion of `mulCutoff` with the Leibniz correction term. -/
def mulCutoffPartial (Ω : Set (EuclideanSpace ℝ (Fin n))) (hη : IsTestFn Ω' η) (i : Fin n) :
    L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (hη.continuous_partialD i).measurable
    (ae_of_all (volume.restrict Ω) (exists_abs_bound_partialD hη i).choose_spec)

/-- The a.e. representative of `mulCutoff`: `mulCutoff Ω hη g =ᵐ x ↦ η x · g x`. -/
theorem mulCutoff_coeFn (hη : IsTestFn Ω' η) (g : L2D Ω) :
    mulCutoff Ω hη g =ᵐ[volume.restrict Ω] fun x => η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- The a.e. representative of `mulCutoffPartial`:
`mulCutoffPartial Ω hη i g =ᵐ x ↦ ∂ᵢη x · g x`. -/
theorem mulCutoffPartial_coeFn (hη : IsTestFn Ω' η) (i : Fin n) (g : L2D Ω) :
    mulCutoffPartial Ω hη i g =ᵐ[volume.restrict Ω] fun x => partialD i η x * (g x : ℝ) :=
  mulCoeffL_coeFn _ _ g

/-- **Cutoff multiplication on the graph space for an ambiently supported cutoff**,
`cutoffMulOn Ω η : H1amb Ω →L H1amb Ω`, encoding the Leibniz rule `∇(η u) = η ∇u + (∇η) u`:
coordinate `0` multiplies by `η`, coordinate `i+1` sends `U` to `η · U_{i+1} + (∂ᵢη) · U₀`.
This is `cutoffMul` (`EllipticPdes.Regularity.cutoffMul`) with the cutoff's support released
from `Ω`. -/
def cutoffMulOn (Ω : Set (EuclideanSpace ℝ (Fin n))) (hη : IsTestFn Ω' η) :
    H1amb Ω →L[ℝ] H1amb Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => L2D Ω)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi
        (Fin.cons ((mulCutoff Ω hη).comp (ContinuousLinearMap.proj 0))
          (fun i => (mulCutoff Ω hη).comp (ContinuousLinearMap.proj i.succ)
            + (mulCutoffPartial Ω hη i).comp (ContinuousLinearMap.proj 0)))).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => L2D Ω)).toContinuousLinearMap)

/-- Coordinate `0` of `cutoffMulOn`: `(cutoffMulOn Ω η U)₀ = η · U₀`. -/
theorem cutoffMulOn_apply_zero (hη : IsTestFn Ω' η) (U : H1amb Ω) :
    (cutoffMulOn Ω hη U) 0 = mulCutoff Ω hη (U 0) := by
  simp only [cutoffMulOn, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_zero, ContinuousLinearMap.proj_apply]

/-- Coordinate `i+1` of `cutoffMulOn`:
`(cutoffMulOn Ω η U)_{i+1} = η · U_{i+1} + (∂ᵢη) · U₀`. -/
theorem cutoffMulOn_apply_succ (hη : IsTestFn Ω' η) (U : H1amb Ω) (i : Fin n) :
    (cutoffMulOn Ω hη U) i.succ
      = mulCutoff Ω hη (U i.succ) + mulCutoffPartial Ω hη i (U 0) := by
  simp only [cutoffMulOn, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.coe_continuousLinearEquiv, PiLp.toLp_apply, ContinuousLinearMap.pi_apply,
    Fin.cons_succ, ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply]

end Multipliers

/-! ### Support calculus for a difference quotient of a test function -/

section Support

variable {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}

/-- The pointwise difference quotient of a smooth function along a fixed vector `v` is
smooth: a translation, a subtraction, and a division by a constant. -/
theorem contDiff_shiftDiffQuotFn (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : EuclideanSpace ℝ (Fin n)) (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ (x + v) - φ x) / h) :=
  ((hφ.comp (contDiff_id.add contDiff_const)).sub hφ).div_const h

/-- The support of a difference quotient along `v` sits inside the union of the back-shifted
support and the support: off both, the function vanishes at `x + v` and at `x`. -/
theorem support_shiftDiffQuotFn_subset (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (h : ℝ) :
    Function.support (fun x => (φ (x + v) - φ x) / h)
      ⊆ (fun x => x + v) ⁻¹' tsupport φ ∪ tsupport φ := by
  intro x hx
  by_contra hc
  have h1 : x + v ∉ tsupport φ := fun hm => hc (Or.inl hm)
  have h2 : x ∉ tsupport φ := fun hm => hc (Or.inr hm)
  refine hx ?_
  change (φ (x + v) - φ x) / h = 0
  rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_self,
    zero_div]

/-- The topological support of a difference quotient along `v` sits inside the union of the
back-shifted topological support and the topological support, a closed set. -/
theorem tsupport_shiftDiffQuotFn_subset (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (h : ℝ) :
    tsupport (fun x => (φ (x + v) - φ x) / h)
      ⊆ (fun x => x + v) ⁻¹' tsupport φ ∪ tsupport φ :=
  closure_minimal (support_shiftDiffQuotFn_subset φ v h)
    (((isClosed_tsupport φ).preimage (by fun_prop)).union (isClosed_tsupport φ))

end Support

/-! ### Tangential difference quotient -/

section Tangential

variable {d : ℕ}

/-- A tangential shift leaves the normal coordinate alone: `(hshift k.succ h) 0 = 0`. Every
tangential direction is `k.succ` for some `k : Fin d`, and `Fin.succ` never hits `0`. -/
theorem hshift_succ_apply_zero (k : Fin d) (h : ℝ) :
    (hshift k.succ h) (0 : Fin (d + 1)) = 0 := by
  simp [hshift, PiLp.smul_apply, (Fin.succ_ne_zero k).symm]

/-- A tangential translation leaves the normal coordinate alone:
`(x + hshift k.succ h) 0 = x 0`. This is the whole geometric content of tangentiality, and it
is what keeps a point on the half-space side of the flat boundary (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 3). -/
theorem add_hshift_succ_apply_zero (k : Fin d) (h : ℝ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    (x + hshift k.succ h) (0 : Fin (d + 1)) = x (0 : Fin (d + 1)) := by
  rw [PiLp.add_apply, hshift_succ_apply_zero, add_zero]

/-- **Tangential difference quotient on `L²` of the half-ball**, `Dₖʰ` for a tangential
direction `k.succ`: the restricted-domain difference quotient
(`EllipticPdes.Regularity.diffQuotD`) of the interior chain, run on `Ω = halfBall d r` and
restricted to directions parallel to the flat boundary (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 3). -/
def tangDiffQuotD (d : ℕ) (r : ℝ) (k : Fin d) (h : ℝ) :
    L2D (halfBall d r) →L[ℝ] L2D (halfBall d r) :=
  diffQuotD k.succ h (measurableSet_halfBall d r)

/-- **Tangential difference quotient on the graph space of the half-ball**, applying
`tangDiffQuotD` in every ambient coordinate. -/
def tangDiffQuotG (d : ℕ) (r : ℝ) (k : Fin d) (h : ℝ) :
    H1amb (halfBall d r) →L[ℝ] H1amb (halfBall d r) :=
  diffQuotG k.succ h (measurableSet_halfBall d r)

/-- The pointwise a.e. formula for the tangential difference quotient:
`Dₖʰ g(x) = ((extendL2 g)(x + h e_{k.succ}) - g(x)) / h`, valid on the half-ball. -/
theorem coeFn_tangDiffQuotD (d : ℕ) (r : ℝ) (k : Fin d) (h : ℝ) (g : L2D (halfBall d r)) :
    (tangDiffQuotD d r k h g : EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
      =ᵐ[volume.restrict (halfBall d r)] fun x =>
        ((extendL2 (measurableSet_halfBall d r) g) (x + hshift k.succ h) - g x) / h :=
  coeFn_diffQuotD k.succ h (measurableSet_halfBall d r) g

/-- Every ambient coordinate of `tangDiffQuotG` is `tangDiffQuotD` applied coordinatewise. -/
@[simp] theorem tangDiffQuotG_apply (d : ℕ) (r : ℝ) (k : Fin d) (h : ℝ)
    (U : H1amb (halfBall d r)) (j : Fin (d + 2)) :
    tangDiffQuotG d r k h U j = tangDiffQuotD d r k h (U j) :=
  diffQuotG_apply k.succ h (measurableSet_halfBall d r) U j

end Tangential

/-! ### Evans' cutoff on the half-ball -/

section Cutoff

variable {d : ℕ}

/-- **Evans' cutoff.** For `0 < r` there is a test function on the ball `B(0, r)`, valued in
`[0, 1]`, equal to `1` on a neighbourhood of `closedBall 0 (r / 2)`. This is exactly the `ζ` of
Evans, *Partial Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 1: `ζ ≡ 1` on
`B(0, 1/2)`, `ζ ≡ 0` off `B(0, 1)`, `0 ≤ ζ ≤ 1`, so `ζ` vanishes near the curved part of `∂U`
and has no constraint on the flat part. The construction is the Urysohn-type cutoff of
`exists_isTestFn_one_nhdsSet_of_isCompact` (`EllipticPdes.Regularity.CutoffTower`), applied to
the compact-in-open pair `closedBall 0 (r / 2) ⊆ ball 0 r`. -/
theorem eqOn_one_closure_halfBall {r : ℝ} (hr : 0 < r)
    {ζ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hζ_one : ∀ᶠ x in 𝓝ˢ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) (r / 2)),
      ζ x = 1) :
    Set.EqOn ζ 1 (closure (halfBall d (r / 2))) := by
  intro x hx
  rw [closure_halfBall d (by linarith : (0:ℝ) < r / 2)] at hx
  exact hζ_one.self_of_nhdsSet x hx.1

/-- **Evans' cutoff.** For `0 < r` there is a test function on the ball `B(0, r)`, valued in
`[0, 1]`, equal to `1` on a neighbourhood of `closedBall 0 (r / 2)` and hence on the whole
closed smaller half-ball, flat part included. This is exactly the `ζ` of Evans, *Partial
Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 1: `ζ ≡ 1` on `B(0, 1/2)`, `ζ ≡
0` off `B(0, 1)`, `0 ≤ ζ ≤ 1`, so `ζ` vanishes near the curved part of `∂U` and has no
constraint on the flat part. The construction is the Urysohn-type cutoff of
`exists_isTestFn_one_nhdsSet_of_isCompact` (`EllipticPdes.Regularity.CutoffTower`), applied to
the compact-in-open pair `closedBall 0 (r / 2) ⊆ ball 0 r`. -/
theorem exists_tangentialCutoff {r : ℝ} (hr : 0 < r) :
    ∃ ζ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      IsTestFn (Metric.ball 0 r) ζ
        ∧ (∀ᶠ x in 𝓝ˢ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) (r / 2)),
            ζ x = 1)
        ∧ Set.EqOn ζ 1 (closure (halfBall d (r / 2)))
        ∧ ∀ x, ζ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ζ, hζ, hζ_one, hζ_Icc⟩ :=
    exists_isTestFn_one_nhdsSet_of_isCompact
      (K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin (d + 1))) (r / 2))
      (U := Metric.ball 0 r) (isCompact_closedBall _ _) Metric.isOpen_ball
      (Metric.closedBall_subset_ball (by linarith))
  exact ⟨ζ, hζ, hζ_one, eqOn_one_closure_halfBall hr hζ_one, hζ_Icc⟩

end Cutoff

/-! ### Cut-off tangential difference quotient as a test function -/

section CutoffDiffQuot

variable {d : ℕ} {r : ℝ} {ζ φ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}

/-- **Tangential difference quotients stay on the half-space side.** The tangential difference
quotient of a test function on the half-ball is supported in the open half-space
`{x | 0 < x 0}`: its support sits inside the union of `tsupport φ` and the back-shifted
`tsupport φ`, and a tangential shift leaves the normal coordinate alone
(`add_hshift_succ_apply_zero`), so both pieces inherit `0 < x 0` from `tsupport φ ⊆ halfBall`.
No smallness condition on `h` is needed, in contrast with the interior case, where a shift of
the cutoff's support has to be kept inside the domain by a margin. This is the geometric
reason the boundary `H²` estimate differentiates in tangential directions alone (Evans,
*Partial Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 3). -/
theorem tsupport_tangDiffQuotFn_subset_halfSpace (hφ : IsTestFn (halfBall d r) φ)
    (k : Fin d) (h : ℝ) :
    tsupport (fun x => (φ (x + hshift k.succ h) - φ x) / h)
      ⊆ {x : EuclideanSpace ℝ (Fin (d + 1)) | 0 < x 0} := by
  refine (tsupport_shiftDiffQuotFn_subset φ (hshift k.succ h) h).trans ?_
  rintro x (hx | hx)
  · rw [Set.mem_preimage] at hx
    have hpos : 0 < (x + hshift k.succ h) (0 : Fin (d + 1)) := (hφ.2.2 hx).2
    rwa [add_hshift_succ_apply_zero k h x] at hpos
  · exact (hφ.2.2 hx).2

/-- **Cutoff of a tangential difference quotient as a test function on the half-ball.**
For Evans' cutoff `ζ` (a test function on `B(0, r)`, reaching the flat boundary) and a test
function `φ` on the half-ball, the product `ζ · Dₖ^h φ` in a tangential direction `k.succ` is
smooth, compactly supported, and supported inside the half-ball: `ζ` supplies the ball
constraint and the tangential difference quotient supplies `0 < x 0`. This holds for **every**
step `h`, so it is the boundary counterpart of `isTestFn_cutoff_diffQuotFn`
(`EllipticPdes.Regularity.RestrictedDiffQuotientMem`) and the fact that makes
`v = -Dₖ^{-h}(ζ² Dₖ^h u)` a legal test element without any trace operator (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.2, Theorem 4, proof step 3). -/
theorem isTestFn_tangentialCutoff_diffQuotFn (hζ : IsTestFn (Metric.ball 0 r) ζ)
    (hφ : IsTestFn (halfBall d r) φ) (k : Fin d) (h : ℝ) :
    IsTestFn (halfBall d r) (fun x => ζ x * ((φ (x + hshift k.succ h) - φ x) / h)) := by
  refine ⟨hζ.1.mul (contDiff_shiftDiffQuotFn hφ.1 (hshift k.succ h) h),
    HasCompactSupport.mul_right hζ.2.1, ?_⟩
  intro x hx
  refine ⟨hζ.2.2 ((closure_mono (Function.support_mul_subset_left _ _)) hx),
    tsupport_tangDiffQuotFn_subset_halfSpace hφ k h
      ((closure_mono (Function.support_mul_subset_right _ _)) hx)⟩

end CutoffDiffQuot

end EllipticPdes.Regularity
