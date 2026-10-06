/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.CoeffBridge
public import EllipticPdes.Regularity.LeibnizWkInfty
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Calculus of test functions and the weak Leibniz rule for a `C¹` weight

The partial derivative of a smooth compactly supported function is again smooth and compactly
supported, so `∂ⱼφ` is an admissible test function wherever `φ` is. The mixed partials of a
smooth function agree, and a class in `L²(V)` is integrable against a test function.

## Main declarations

* `contDiff_partialD`, `hasCompactSupport_partialD`, `isTest_partialD`: `∂ⱼφ` is a test
  function.
* `partialD_partialD_swap`: the mixed partials of a smooth function agree.
* `integrable_mul_testFn`: an `L²(V)` class is integrable against a test function.
* `HasWeakDerivOn.mul_contDiff_left`: the weak Leibniz rule for a `C¹` weight.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Test-function calculus -/

/-- The partial derivative of a `C^∞` function is `C^∞`. -/
theorem contDiff_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := (contDiff_infty_iff_fderiv.mp hφ).2
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
  exact hf.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ)))

/-- The partial derivative of a compactly-supported function has compact support. -/
theorem hasCompactSupport_partialD {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : HasCompactSupport φ) (j : Fin d) : HasCompactSupport (partialD j φ) :=
  hφ.mono' ((subset_tsupport (partialD j φ)).trans (tsupport_partialD_subset j φ))

/-- `∂ⱼφ` is again an admissible `HasWeakDerivOn` test function on `V` when `φ` is. -/
theorem isTest_partialD {V : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hV : tsupport φ ⊆ V) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (partialD j φ) ∧ HasCompactSupport (partialD j φ)
      ∧ tsupport (partialD j φ) ⊆ V :=
  ⟨contDiff_partialD hc j, hasCompactSupport_partialD hcs j,
    (tsupport_partialD_subset j φ).trans hV⟩

/-- **Integrability of an `L²` class against a test function.** Hölder with the two exponents `2`
and the continuous compactly supported factor in `L²`. -/
theorem integrable_mul_testFn {V : Set (EuclideanSpace ℝ (Fin d))} (F : L2D V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφc : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcs : HasCompactSupport φ) :
    Integrable (fun x => (F x : ℝ) * φ x) (volume.restrict V) := by
  have : ENNReal.HolderTriple (2 : ENNReal) 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  exact (Lp.memLp F).integrable_mul
    ((hφc.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hφcs).restrict V)

/-- An integral over `Ω` of an integrand vanishing off `W ⊆ Ω` is an integral over `W`. -/
theorem setIntegral_shrink_of_forall_eq_zero
    {W Ω : Set (EuclideanSpace ℝ (Fin d))} (hWΩ : W ⊆ Ω)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ∀ x, x ∉ W → F x = 0) :
    ∫ x in Ω, F x = ∫ x in W, F x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hF x (fun hc => hx (hWΩ hc))),
    setIntegral_eq_integral_of_forall_compl_eq_zero hF]

/-- The restriction to `V ⊆ Ω` of the whole-space extension of an `L²(Ω)` class agrees with the
class itself on `V`. -/
theorem coeFn_restrictL2_extendL2_of_subset {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) (g : L2D Ω) :
    (restrictL2 (Ω := V) (extendL2 hΩm g) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict V] (g : EuclideanSpace ℝ (Fin d) → ℝ) := by
  filter_upwards [coeFn_restrictL2 (Ω := V) (extendL2 hΩm g),
    ae_restrict_of_ae (coeFn_extendL2 hΩm g), ae_restrict_mem hVm] with x h1 h2 h3
  rw [h1, h2, Set.indicator_of_mem (hVΩ h3)]

/-- An integral over `Ω` of a weight times an `L²(Ω)` class times a function vanishing off
`V ⊆ Ω` is the integral over `V` against the restricted extension of the class. -/
theorem setIntegral_mul_restrictL2_extendL2 {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hΩm : MeasurableSet Ω) (hVm : MeasurableSet V) (hVΩ : V ⊆ Ω) (g : L2D Ω)
    (c w : EuclideanSpace ℝ (Fin d) → ℝ) (hw : ∀ x, x ∉ V → w x = 0) :
    ∫ x in Ω, c x * (g x : ℝ) * w x
      = ∫ x in V, c x * (restrictL2 (Ω := V) (extendL2 hΩm g) x : ℝ) * w x := by
  rw [setIntegral_shrink_of_forall_eq_zero hVΩ (fun x hx => by rw [hw x hx, mul_zero])]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_restrictL2_extendL2_of_subset hΩm hVm hVΩ g] with x hx
  rw [hx]

/-- **Mixed-partial symmetry for smooth functions.** `∂_ℓ ∂ⱼφ = ∂ⱼ ∂_ℓφ`.

`partialD ℓ φ` is `fun y => fderiv ℝ φ y (eℓ)`, so `fderiv_clm_apply` reads its derivative off
the second Fréchet derivative, and `ContDiffAt.isSymmSndFDerivAt` swaps the two arguments. -/
lemma partialD_partialD_swap {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (j ℓ : Fin d) :
    partialD ℓ (partialD j φ) = partialD j (partialD ℓ φ) := by
  have hFd : Differentiable ℝ (fderiv ℝ φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2).differentiable (by simp)
  have hentry : ∀ (a b : Fin d) (x : EuclideanSpace ℝ (Fin d)),
      partialD a (partialD b φ) x
        = fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    intro a b x
    have hrw : partialD b φ = fun y => (fderiv ℝ φ y) (EuclideanSpace.single b 1) := rfl
    simp only [partialD, hrw]
    rw [fderiv_clm_apply (hFd x) (differentiableAt_const _)]
    simp [ContinuousLinearMap.flip_apply]
  funext x
  rw [hentry ℓ j x, hentry j ℓ x]
  refine (hφ.contDiffAt.isSymmSndFDerivAt ?_) _ _
  simp only [minSmoothness_of_isRCLikeNormedField]
  exact WithTop.coe_le_coe.mpr le_top

/-- **Weak Leibniz rule with a `C¹` weight.** If `g` has weak `ℓ`-derivative `g'` on `V`, and
`a` is `C¹` with `a` and `∂_ℓ a` essentially bounded, then `a·g` has weak `ℓ`-derivative
`(∂_ℓ a)·g + a·g'` on `V`. This is `HasWeakDerivOn.mul_isWkInfty_left` for the weak derivative
`∂_ℓ a` of a `C¹` function. -/
theorem HasWeakDerivOn.mul_contDiff_left {V : Set (EuclideanSpace ℝ (Fin d))}
    (_hVm : MeasurableSet V) (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {a : EuclideanSpace ℝ (Fin d) → ℝ} (ha : ContDiff ℝ 1 a)
    {Ma Mda : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ Ma)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |partialD ℓ a x| ≤ Mda)
    (ag : Lp ℝ 2 (volume.restrict V))
    (hag : ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ))
    (dag : Lp ℝ 2 (volume.restrict V))
    (hdag : dag =ᵐ[volume.restrict V]
              fun x => partialD ℓ a x * (g x : ℝ) + a x * (g' x : ℝ)) :
    HasWeakDerivOn V ℓ ag dag :=
  HasWeakDerivOn.mul_isWkInfty_left ℓ hg ha.continuous.measurable
    ((ha.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable
    (hasWeakPartial_partialD ha ℓ) haM hdaM ag hag dag hdag

end EllipticPdes.Regularity
