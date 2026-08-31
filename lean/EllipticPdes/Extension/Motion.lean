/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Embedding.WeakGradient
import EllipticPdes.Sobolev.Basic

/-!
# Rigid motion of a boundary chart

A boundary chart relabels and reorients the coordinate axes before reading the domain off a
graph, and that relabelling and reorientation is a linear isometry of the whole space. This
file moves a weak gradient through one.

A linear isometry is its own derivative, so the chain rule sends the gradient to its transpose
applied to the gradient, which in coordinates is the sum over the directions the isometry sends
the `k`-th one to. The reflection of `Extension/Reflect.lean` is the case where that sum has a
single term and a sign; the general case needs the sum, and the finite sum has to travel
through an integral, which is where the integrability hypotheses enter.

## Main declarations

* `EllipticPdes.Extension.clm_apply_eq_sum`: a continuous linear functional is the sum of its
  values on the standard directions.
* `EllipticPdes.Extension.partialD_comp_linearIsometry`: the chain rule through an isometry.
* `EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry`: the weak gradient through an
  isometry.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §C.1 (p. 665), where the relabelling
and reorientation of the axes appears; Y. Guo, *Partial Differential Equations I and II*
(Course Lecture Notes), Theorem III.2.2 (p. 20).
-/

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn integrableOn_mul_bounded)
open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- A vector is the sum of its coordinates against the standard directions. -/
theorem sum_smul_single (v : EuclideanSpace ℝ (Fin d)) :
    ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
  ext m
  simp [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]

/-- A continuous linear functional is the sum of its values on the standard directions. -/
theorem clm_apply_eq_sum (T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    T v = ∑ i, v i * T (EuclideanSpace.single i (1 : ℝ)) := by
  conv_lhs => rw [← sum_smul_single v]
  rw [map_sum]
  simp [smul_eq_mul]

/-- **Partial derivatives through a linear isometry.** -/
theorem partialD_comp_linearIsometry {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : Differentiable ℝ φ) (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (k : Fin d) (y : EuclideanSpace ℝ (Fin d)) :
    partialD k (fun z => φ (e z)) y
      = ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * partialD i φ (e y) := by
  have hcomp : HasFDerivAt (fun z => φ (e z))
      ((fderiv ℝ φ (e y)).comp (e.toContinuousLinearEquiv :
        EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) y :=
    (hφ (e y)).hasFDerivAt.comp y e.toContinuousLinearEquiv.hasFDerivAt
  rw [partialD, hcomp.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact clm_apply_eq_sum (fderiv ℝ φ (e y)) _

/-- **Weak gradient through a linear isometry.** The isometry is its own derivative, so the
gradient transforms by its transpose, which in coordinates is the sum over the directions the
isometry sends the `k`-th one to. -/
theorem hasWeakGradOn_comp_linearIsometry {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g)
    (e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    HasWeakGradOn ((e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B)
      (fun y => u (e y))
      (fun k y => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) := by
  classical
  intro φ hφ hφcs hφs k
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = fun x => φ (e.symm x) := ⟨_, rfl⟩
  have hψsm : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψ]; exact hφ.comp e.symm.toContinuousLinearEquiv.contDiff
  have hψcs : HasCompactSupport ψ := by
    rw [hψ]; exact hφcs.comp_homeomorph e.symm.toHomeomorph
  have hψS : ∀ y, ψ (e y) = φ y := by
    intro y; rw [hψ]; simp
  have hψs : tsupport ψ ⊆ B := by
    have hsub : tsupport ψ ⊆ (e.symm : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        ⁻¹' tsupport φ := by
      refine closure_minimal ?_ (IsClosed.preimage e.symm.continuous isClosed_closure)
      intro x hx
      refine Set.mem_preimage.mpr (subset_tsupport φ ?_)
      simp only [hψ, Function.mem_support] at hx
      exact hx
    intro x hx
    have h2 := hφs (hsub hx)
    simp only [Set.mem_preimage] at h2
    rwa [e.apply_symm_apply] at h2
  have hchain : ∀ y, partialD k φ y
      = ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * partialD i ψ (e y) := by
    intro y
    have h := partialD_comp_linearIsometry (hψsm.differentiable (by simp)) e k y
    have hfun : (fun z => ψ (e z)) = φ := funext hψS
    rwa [hfun] at h
  -- the change of variables
  have hmp : MeasurePreserving (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
      volume volume := e.measurePreserving
  have hme : MeasurableEmbedding
      (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :=
    e.toHomeomorph.measurableEmbedding
  have hcv : ∀ F : EuclideanSpace ℝ (Fin d) → ℝ,
      ∫ y in (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B, F (e y)
        = ∫ x in B, F x := fun F => hmp.setIntegral_preimage_emb hme F B
  -- bounds and integrability of the pieces
  have hψc : Continuous ψ := hψsm.continuous
  have hdc : ∀ i, Continuous (partialD i ψ) := fun i =>
    ((hψsm.of_le (by exact_mod_cast le_top)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have hdcs : ∀ i, HasCompactSupport (partialD i ψ) := fun i =>
    (hψcs.fderiv ℝ).comp_left
      (g := fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ => T (EuclideanSpace.single i (1 : ℝ)))
      (by simp)
  have hintU : ∀ i, IntegrableOn (fun x =>
      u x * (e (EuclideanSpace.single k (1 : ℝ)) i * partialD i ψ x)) B volume := by
    intro i
    obtain ⟨N, hN⟩ := (hdcs i).exists_bound_of_continuous (hdc i)
    exact integrableOn_mul_bounded hu (continuous_const.mul (hdc i))
      (C := ‖e (EuclideanSpace.single k (1 : ℝ)) i‖ * N) (fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hN x) (norm_nonneg _))
  have hintG : ∀ i, IntegrableOn (fun x =>
      e (EuclideanSpace.single k (1 : ℝ)) i * (g i x * ψ x)) B volume := by
    intro i
    obtain ⟨P, hP⟩ := hψcs.exists_bound_of_continuous hψc
    exact ((integrableOn_mul_bounded (hgi i) hψc hP).const_mul _)
  -- both sides, moved onto `B`
  have hLeft : ∫ y in (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B,
        u (e y) * partialD k φ y
      = ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * ∫ x in B, u x * partialD i ψ x := by
    have step1 : ∫ y in (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B,
          u (e y) * partialD k φ y
        = ∫ x in B, ∑ i, u x * (e (EuclideanSpace.single k (1 : ℝ)) i * partialD i ψ x) := by
      rw [← hcv fun x => ∑ i, u x * (e (EuclideanSpace.single k (1 : ℝ)) i * partialD i ψ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [hchain y, Finset.mul_sum]
    rw [step1, integral_finsetSum _ fun i _ => hintU i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hRight : ∫ y in (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B,
        (∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) * φ y
      = ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * ∫ x in B, g i x * ψ x := by
    have step1 : ∫ y in (e : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) ⁻¹' B,
          (∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * g i (e y)) * φ y
        = ∫ x in B, ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * (g i x * ψ x) := by
      rw [← hcv fun x => ∑ i, e (EuclideanSpace.single k (1 : ℝ)) i * (g i x * ψ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [hψS y, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [step1, integral_finsetSum _ fun i _ => hintG i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]
  rw [hLeft, hRight, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hwg ψ hψsm hψcs hψs i]
  ring

end EllipticPdes.Extension
