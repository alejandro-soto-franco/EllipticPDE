/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Extension.Cutoff
public import EllipticPdes.Extension.Reflect
public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Extension.Basic

/-!
# Half space and its interface

The extension of a Sobolev class across a flat boundary is by reflection, and what has to be
proved is that the reflected class has a weak gradient across the interface. The identity of a
weak gradient on the open half space applies only to test functions supported strictly inside
it, so the test function is first multiplied by `slabCut ℓ ε`, with `ℓ` the `j`-th coordinate,
and the slab is then let shrink.

Two terms survive the product rule. The one with the cutoff's own derivative vanishes
identically in the directions along the interface, since the cutoff depends on the `j`-th
coordinate alone. In the remaining direction it is the boundary term, and it vanishes in the
limit whenever the test function vanishes on the interface, which is exactly what the odd part
of a reflection does.

The half space is `{x | 0 < ℓ x}` for a nonzero continuous linear functional `ℓ` on a
finite-dimensional real normed space with an additive Haar measure, and the weak derivative is
along a vector `w` (`HasWeakDerivAlong`). The coordinate statements, for `ℓ` the `j`-th
coordinate and `w` a basis vector, are the instances `integral_partialD_of_ne` and
`integral_partialD_of_eq`.

## Main declarations

* `EllipticPdes.Extension.posHalfSpace`: the open half space `{0 < ℓ x}`.
* `EllipticPdes.Extension.integral_fderiv_apply_of_apply_eq_zero`: no boundary term along the
  interface.
* `EllipticPdes.Extension.integral_fderiv_apply_of_vanishes`: none across the interface either,
  for a test function vanishing on the interface.
* `EllipticPdes.Extension.halfSpace`: the coordinate half space `{xⱼ > 0}`.
* `EllipticPdes.Extension.volume_interface`: the interface is null.
* `EllipticPdes.Extension.integral_partialD_of_ne` and
  `EllipticPdes.Extension.integral_partialD_of_eq`: the coordinate forms.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.4 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Sobolev (partialD)
open EllipticPdes.Embedding (HasWeakGradOn HasWeakDerivAlong hasWeakGradOn_iff)

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {u g ψ : E → ℝ}

/-- **Open half space** `{0 < ℓ x}` of a continuous linear functional. -/
def posHalfSpace (ℓ : E →L[ℝ] ℝ) : Set E := {x | 0 < ℓ x}

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- `posHalfSpace ℓ` is open. -/
theorem isOpen_posHalfSpace (ℓ : E →L[ℝ] ℝ) : IsOpen (posHalfSpace ℓ) :=
  isOpen_lt continuous_const ℓ.continuous

/-- `posHalfSpace ℓ` is measurable. -/
theorem measurableSet_posHalfSpace (ℓ : E →L[ℝ] ℝ) : MeasurableSet (posHalfSpace ℓ) :=
  (isOpen_posHalfSpace ℓ).measurableSet

/-- **A hyperplane is null.** The kernel of a nonzero linear functional is a proper subspace,
and a proper subspace has measure zero for an additive Haar measure. -/
theorem measure_ker_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {ℓ : E →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) : μ {x | ℓ x = 0} = 0 :=
  Measure.addHaar_submodule μ (LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)) fun h =>
    hℓ (ContinuousLinearMap.coe_injective (LinearMap.ker_eq_top.1 h))

/-- **A `C¹` function vanishing on a hyperplane is bounded by its gradient and the distance to
it.** This is what makes the boundary term vanish in the limit. -/
theorem abs_le_of_vanishes_on_hyperplane {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : E → ℝ} (hψ : Differentiable ℝ ψ) {M : ℝ} (hM : ∀ z, ‖fderiv ℝ ψ z‖ ≤ M)
    {ℓ : E →L[ℝ] ℝ} {v : E} (hv : ℓ v = 1) (hzero : ∀ z, ℓ z = 0 → ψ z = 0) (x : E) :
    |ψ x| ≤ M * ‖v‖ * |ℓ x| := by
  have h := (convex_univ (𝕜 := ℝ) (E := E)).norm_image_sub_le_of_norm_fderiv_le (f := ψ)
    (fun z _ => hψ z) (fun z _ => hM z) (mem_univ (x - ℓ x • v)) (mem_univ x)
  rw [hzero (x - ℓ x • v) (by simp [hv]), sub_zero, sub_sub_cancel, norm_smul,
    Real.norm_eq_abs] at h
  calc |ψ x| ≤ M * (|ℓ x| * ‖v‖) := by simpa using h
    _ = M * ‖v‖ * |ℓ x| := by ring

variable {ℓ : E →L[ℝ] ℝ} {w : E}

omit [OpensMeasurableSpace E] in
/-- The identity at each `ε`: multiplied by the cutoff, the test function is supported strictly
inside the half space, where the weak derivative applies. -/
private theorem cutoff_identity (hwg : HasWeakDerivAlong μ w (posHalfSpace ℓ) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in posHalfSpace ℓ, u x * (fderiv ℝ (slabCut ℓ ε) x w * ψ x
        + slabCut ℓ ε x * fderiv ℝ ψ x w) ∂μ
      = - ∫ x in posHalfSpace ℓ, g x * (slabCut ℓ ε x * ψ x) ∂μ := by
  have h := hwg (fun x => slabCut ℓ ε x * ψ x) ((contDiff_slabCut _ ε).mul hψ) hψcs.mul_left
    (tsupport_mul_slabCut_subset hε ψ)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change _ = u x * fderiv ℝ (slabCut ℓ ε * ψ) x w
  rw [(((contDiff_slabCut ℓ ε).differentiable (by simp) x).hasFDerivAt.mul
    (hψ.differentiable (by simp) x).hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- The cutoffs of width `1 / (n + 1)` converge to `1` on the open half space. -/
private theorem tendsto_slabCut {x : E} (hx : x ∈ posHalfSpace ℓ) :
    Tendsto (fun n : ℕ => slabCut ℓ ((n + 1 : ℝ)⁻¹) x) atTop (𝓝 1) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ℓ x)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  refine (slabCut_eq_one (by positivity) ?_).symm
  have hmn : (2 : ℝ) / ℓ x < (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [div_lt_iff₀ hx] at hmn
  rw [inv_eq_one_div, mul_one_div, div_le_iff₀ (by positivity)]
  linarith

/-- **Weak-derivative identity against a test function that need not vanish near the
interface**, given that the boundary term it leaves goes to zero. -/
private theorem integral_fderiv_apply_aux (hu : IntegrableOn u (posHalfSpace ℓ) μ)
    (hg : IntegrableOn g (posHalfSpace ℓ) μ) (hwg : HasWeakDerivAlong μ w (posHalfSpace ℓ) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hbdry : Tendsto (fun n : ℕ => ∫ x in posHalfSpace ℓ,
        u x * (fderiv ℝ (slabCut ℓ ((n + 1 : ℝ)⁻¹)) x w * ψ x) ∂μ) atTop (𝓝 0)) :
    ∫ x in posHalfSpace ℓ, u x * fderiv ℝ ψ x w ∂μ = - ∫ x in posHalfSpace ℓ, g x * ψ x ∂μ := by
  set cut : ℕ → E → ℝ := fun n => slabCut ℓ ((n + 1 : ℝ)⁻¹) with hcut
  have hcc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (cut n) := fun n => contDiff_slabCut _ _
  have hdψ : Continuous (fun x => fderiv ℝ ψ x w) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψcs : HasCompactSupport (fun x => fderiv ℝ ψ x w) := hψcs.fderiv_apply (𝕜 := ℝ) w
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨N, hN⟩ := hdψcs.exists_bound_of_continuous hdψ
  have hlim1 := tendsto_setIntegral_mul (measurableSet_posHalfSpace ℓ) hu
    (f := fun n x => cut n x * fderiv ℝ ψ x w) (f' := fun x => fderiv ℝ ψ x w)
    (fun n => (hcc n).continuous.mul hdψ) (C := N)
    (fun n x => by simpa using norm_mul_le_of_le (norm_slabCut_le_one _ _ x) (hN x))
    (fun x hx => by simpa using (tendsto_slabCut hx).mul_const (fderiv ℝ ψ x w))
  have hlim2 := tendsto_setIntegral_mul (measurableSet_posHalfSpace ℓ) hg
    (f := fun n x => cut n x * ψ x) (f' := ψ)
    (fun n => (hcc n).continuous.mul hψ.continuous) (C := M)
    (fun n x => by simpa using norm_mul_le_of_le (norm_slabCut_le_one _ _ x) (hM x))
    (fun x hx => by simpa using (tendsto_slabCut hx).mul_const (ψ x))
  have hsplit : ∀ n : ℕ, (∫ x in posHalfSpace ℓ, u x * (fderiv ℝ (cut n) x w * ψ x) ∂μ)
      + (∫ x in posHalfSpace ℓ, u x * (cut n x * fderiv ℝ ψ x w) ∂μ)
      = - ∫ x in posHalfSpace ℓ, g x * (cut n x * ψ x) ∂μ := fun n => by
    have hb1 : IntegrableOn (fun x => u x * (fderiv ℝ (cut n) x w * ψ x)) (posHalfSpace ℓ) μ :=
      hu.mul_of_hasCompactSupport (((hcc n).continuous_fderiv (by simp)).clm_apply
        continuous_const |>.mul hψ.continuous) hψcs.mul_left
    have hb2 : IntegrableOn (fun x => u x * (cut n x * fderiv ℝ ψ x w)) (posHalfSpace ℓ) μ :=
      hu.mul_of_hasCompactSupport ((hcc n).continuous.mul hdψ) hdψcs.mul_left
    rw [← integral_add hb1 hb2, ← cutoff_identity hwg hψ hψcs (by positivity)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  exact tendsto_nhds_unique
    ((by simpa using hbdry.add hlim1 : Tendsto _ atTop _).congr hsplit) hlim2.neg

/-- **No boundary term along the interface.** If `ℓ w = 0` the cutoff has no derivative along
`w`, so the identity passes to a test function that need not vanish near the interface. -/
theorem integral_fderiv_apply_of_apply_eq_zero (hw : ℓ w = 0)
    (hu : IntegrableOn u (posHalfSpace ℓ) μ) (hg : IntegrableOn g (posHalfSpace ℓ) μ)
    (hwg : HasWeakDerivAlong μ w (posHalfSpace ℓ) u g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) :
    ∫ x in posHalfSpace ℓ, u x * fderiv ℝ ψ x w ∂μ = - ∫ x in posHalfSpace ℓ, g x * ψ x ∂μ := by
  refine integral_fderiv_apply_aux hu hg hwg hψ hψcs ?_
  simp [fderiv_slabCut, hw]

/-- **No boundary term across the interface either**, for a test function vanishing on the
interface. Where the cutoff's derivative is `C/ε` the test function is at most `2ε` times its
gradient, so the product is bounded uniformly and supported in a slab that shrinks to nothing. -/
theorem integral_fderiv_apply_of_vanishes {v : E} (hv : ℓ v = 1)
    (hu : IntegrableOn u (posHalfSpace ℓ) μ) (hg : IntegrableOn g (posHalfSpace ℓ) μ)
    (hwg : HasWeakDerivAlong μ v (posHalfSpace ℓ) u g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) (hzero : ∀ z, ℓ z = 0 → ψ z = 0) :
    ∫ x in posHalfSpace ℓ, u x * fderiv ℝ ψ x v ∂μ = - ∫ x in posHalfSpace ℓ, g x * ψ x ∂μ := by
  refine integral_fderiv_apply_aux hu hg hwg hψ hψcs ?_
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_smoothTransition
  obtain ⟨M, hM⟩ := (hψcs.fderiv ℝ).exists_bound_of_continuous
    (hψ.continuous_fderiv (by simp))
  have hcut : ∀ (n : ℕ) (x : E),
      ‖fderiv ℝ (slabCut ℓ ((n + 1 : ℝ)⁻¹)) x v * ψ x‖ ≤ 2 * C * (M * ‖v‖) := by
    intro n x
    have hε : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
    rw [norm_mul]
    by_cases hcase : ℓ x ∈ Icc ((n + 1 : ℝ)⁻¹) (2 * (n + 1 : ℝ)⁻¹)
    · have hx : 0 < ℓ x := hε.trans_le hcase.1
      have h1 : |fderiv ℝ (slabCut ℓ ((n + 1 : ℝ)⁻¹)) x v| ≤ C / ((n : ℝ) + 1)⁻¹ := by
        simpa [hv] using abs_fderiv_slabCut_le (ℓ := ℓ) hε hC x v
      have h2 : |ψ x| ≤ M * ‖v‖ * (2 * ((n : ℝ) + 1)⁻¹) := by
        have := abs_le_of_vanishes_on_hyperplane (hψ.differentiable (by simp)) hM hv hzero x
        rw [abs_of_pos hx] at this
        exact this.trans (by gcongr; exact hcase.2)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ C / ((n : ℝ) + 1)⁻¹ * (M * ‖v‖ * (2 * ((n : ℝ) + 1)⁻¹)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 2 * C * (M * ‖v‖) := by field_simp
    · rw [fderiv_slabCut_eq_zero_of_notMem hε hcase]
      simp only [zero_mul, norm_zero]
      positivity
  have h := tendsto_setIntegral_mul (measurableSet_posHalfSpace ℓ) hu
    (f := fun (n : ℕ) x => fderiv ℝ (slabCut ℓ ((n + 1 : ℝ)⁻¹)) x v * ψ x)
    (f' := fun _ => 0)
    (fun n => (((contDiff_slabCut _ _).continuous_fderiv (by simp)).clm_apply
      continuous_const).mul hψ.continuous)
    (C := 2 * C * (M * ‖v‖)) hcut fun x hx => ?_
  · simpa using h
  · obtain ⟨m, hm⟩ := exists_nat_gt (2 / ℓ x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hmn : (2 : ℝ) / ℓ x < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ hx] at hmn
    have hgt : 2 * ((n : ℝ) + 1)⁻¹ < ℓ x := by
      rw [inv_eq_one_div, mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
    rw [fderiv_slabCut_eq_zero_of_notMem (by positivity) (fun h => h.2.not_gt hgt), zero_mul]

end General

variable {d : ℕ}

/-- **Open half space above the interface `{xⱼ = 0}`.** -/
def halfSpace (j : Fin d) : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < x j}

/-- `halfSpace j` is the half space of the `j`-th coordinate functional. -/
theorem halfSpace_eq_posHalfSpace (j : Fin d) :
    halfSpace j = posHalfSpace (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
  rfl

/-- `halfSpace j` is open. -/
theorem isOpen_halfSpace (j : Fin d) : IsOpen (halfSpace j) :=
  isOpen_posHalfSpace (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)

/-- `halfSpace j` is measurable. -/
theorem measurableSet_halfSpace (j : Fin d) : MeasurableSet (halfSpace j) :=
  (isOpen_halfSpace j).measurableSet

/-- **Nullity of the interface**, being a hyperplane. -/
theorem volume_interface (j : Fin d) :
    volume {x : EuclideanSpace ℝ (Fin d) | x j = 0} = 0 :=
  measure_ker_eq_zero volume (ℓ := EuclideanSpace.proj j) fun h => by
    simpa using DFunLike.congr_fun h (EuclideanSpace.single j (1 : ℝ))

variable {j : Fin d} {u : EuclideanSpace ℝ (Fin d) → ℝ}
  {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- **No boundary term along the interface** (coordinate form of
`integral_fderiv_apply_of_apply_eq_zero`). -/
theorem integral_partialD_of_ne {k : Fin d} (hk : k ≠ j)
    (hu : IntegrableOn u (halfSpace j) volume) (hg : IntegrableOn (g k) (halfSpace j) volume)
    (hwg : HasWeakGradOn (halfSpace j) u g) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψcs : HasCompactSupport ψ) :
    ∫ x in halfSpace j, u x * partialD k ψ x = - ∫ x in halfSpace j, g k x * ψ x :=
  integral_fderiv_apply_of_apply_eq_zero (ℓ := EuclideanSpace.proj j) (by simp [hk.symm]) hu hg
    ((hasWeakGradOn_iff.1 hwg) k) hψ hψcs

/-- **No boundary term in the remaining direction either**, for a test function vanishing on the
interface (coordinate form of `integral_fderiv_apply_of_vanishes`). -/
theorem integral_partialD_of_eq (hu : IntegrableOn u (halfSpace j) volume)
    (hg : IntegrableOn (g j) (halfSpace j) volume) (hwg : HasWeakGradOn (halfSpace j) u g)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψcs : HasCompactSupport ψ)
    (hzero : ∀ z : EuclideanSpace ℝ (Fin d), z j = 0 → ψ z = 0) :
    ∫ x in halfSpace j, u x * partialD j ψ x = - ∫ x in halfSpace j, g j x * ψ x :=
  integral_fderiv_apply_of_vanishes (ℓ := EuclideanSpace.proj j) (by simp) hu hg
    ((hasWeakGradOn_iff.1 hwg) j) hψ hψcs hzero

end EllipticPdes.Extension
