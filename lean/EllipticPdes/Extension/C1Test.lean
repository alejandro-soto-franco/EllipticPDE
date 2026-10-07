/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.Mollifier
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Extension.Basic
public import EllipticPdes.Sobolev.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Integration by parts against a `C¹` test function

`HasWeakGradOn` asks for the integration-by-parts identity against smooth test functions. The
extension operator needs it against a `C¹` one: a boundary chart of a `C¹` domain is `C¹`, so a
smooth test function pulled back through it is `C¹` and no better.

Mollification supplies the smooth test functions. The mollification of a `C¹` class of compact
support is smooth, its support sits in a closed thickening of the original, its partial
derivatives are the mollified partial derivatives, and both stay bounded by the suprema of the
originals while converging pointwise. Dominated convergence passes the identity.

## Main declarations

* `EllipticPdes.Extension.partialD_convolution_normed`: the partial derivative of a
  mollification is the mollification of the partial derivative.
* `EllipticPdes.Extension.hasWeakGradOn_contDiffOne`: the identity of a weak gradient, against
  a `C¹` test function.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Set
open scoped NNReal ENNReal Convolution Pointwise

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

local notation "Lsm" => ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)



/-- **Partial derivative of a mollification.** For `ψ` of class `C¹` with compact support,
`ρ ⋆ ψ` is differentiable and its partial derivatives are the mollified partial derivatives. -/
theorem partialD_convolution_normed (ρ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (k : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD k (ρ.normed volume ⋆[Lsm, volume] ψ) x
      = (ρ.normed volume ⋆[Lsm, volume] (partialD k ψ)) x := by
  have hρli : LocallyIntegrable (ρ.normed volume) volume :=
    (ρ.contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous.locallyIntegrable
  have hfd := hψcs.hasFDerivAt_convolution_right (L := Lsm) hρli hψ x
  rw [partialD, hfd.fderiv,
    convolution_precompR_apply Lsm hρli (hψcs.fderiv ℝ) (hψ.continuous_fderiv one_ne_zero) x
      (EuclideanSpace.single k (1 : ℝ))]
  rfl

/-- **Integration by parts against a `C¹` test function.** A weak gradient on an open set
satisfies its defining identity against every `C¹` function of compact support inside the set,
and not only against the smooth ones the definition names. -/
theorem hasWeakGradOn_contDiffOne {B : Set (EuclideanSpace ℝ (Fin d))} (hBopen : IsOpen B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (hwg : HasWeakGradOn B u g)
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψcs : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ B) (k : Fin d) :
    ∫ x in B, u x * partialD k ψ x = - ∫ x in B, g k x * ψ x := by
  obtain ⟨ε, hε, hsub⟩ := hψcs.isCompact.exists_cthickening_subset_open hBopen hψs
  have hdcs : HasCompactSupport (partialD k ψ) := hψcs.partialD k
  have hdc : Continuous (partialD k ψ) := hψ.continuous_partialD one_ne_zero k
  obtain ⟨M, hM⟩ := hψcs.exists_bound_of_continuous hψ.continuous
  obtain ⟨N, hN⟩ := hdcs.exists_bound_of_continuous hdc
  set ρ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    fun n => mollifier hε n with hρ
  set ψn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => (ρ n).normed volume ⋆[Lsm, volume] ψ with hψn
  have hsm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := fun n =>
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left (L := Lsm) (ρ n).contDiff_normed
      hψ.continuous.locallyIntegrable
  have hrOut := tendsto_rOut_mollifier (E := EuclideanSpace ℝ (Fin d)) hε
  refine integral_eq_neg_integral_of_tendsto hBopen.measurableSet hu (hgi k)
    (F := fun n => partialD k (ψn n)) (G := ψn) (fun n => (hsm n).continuous_partialD (by simp) k)
    (fun n => (hsm n).continuous) (N := N) (P := M)
    (fun n x => ?_) (fun n x => norm_normed_convolution_le (ρ n) hψ.continuous hM x)
    (fun x _ => ?_) (fun x _ => ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := volume) hrOut hψ.continuous x) (fun n => ?_)
  · rw [partialD_convolution_normed (ρ n) hψ hψcs k x]
    exact norm_normed_convolution_le (ρ n) hdc hN x
  · exact (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (φ := ρ)
      hrOut hdc x).congr fun n => (partialD_convolution_normed (ρ n) hψ hψcs k x).symm
  · refine hwg (ψn n) (hsm n) (HasCompactSupport.convolution (L := Lsm)
      (ρ n).hasCompactSupport_normed hψcs) ((tsupport_normed_convolution_subset (ρ n) hψcs).trans
      (fun x hx => hsub (cthickening_mono (rOut_mollifier_le hε n) _ hx))) k

end EllipticPdes.Extension
