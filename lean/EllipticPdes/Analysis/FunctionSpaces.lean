/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.ExtendFrom
public import EllipticPdes.Sobolev.WeakDerivMulti

/-!
# Function spaces and Hölder's inequality

Evans defines `C^k(Ū)` as the functions of class `C^k(U)` whose derivatives up to order `k`
are uniformly continuous on bounded subsets of `U`, and remarks that each such derivative
extends continuously to `Ū`. He defines `L^p_loc(U)` as the functions in `L^p(V)` for every
`V ⊂⊂ U`. This file states both definitions as Evans does and proves the remark on the
extension, the identification of `L^1_loc` with Mathlib's local integrability, and Hölder's
inequality in the form of Appendix B.

## Main declarations

* `EllipticPdes.Analysis.classicalDeriv`: the classical derivative `D^α u` of a multi-index.
* `EllipticPdes.Analysis.CkBar`: Evans's `C^k(Ū)`.
* `EllipticPdes.Analysis.CkBar.exists_extension`: each `D^α u` extends continuously to `Ū`.
* `EllipticPdes.Analysis.MemLpLoc`: Evans's `L^p_loc(U)`.
* `EllipticPdes.Analysis.memLpLoc_one_iff`: `L^1_loc(U)` is local integrability on `U`.
* `EllipticPdes.Analysis.integral_abs_mul_le`: Hölder's inequality for conjugate exponents.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Appendix A (notation for function
spaces, p. 702) and Appendix B (e) (Hölder's inequality, p. 706).
-/

@[expose] public section

open Filter Topology MeasureTheory
open scoped ENNReal Uniformity

noncomputable section

namespace EllipticPdes.Analysis

variable {d k : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} {u v : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The classical derivative `D^α u` of a multi-index `α`, as the iterated partial derivative
in the order convention of `Sobolev.iterPartialD`. -/
def classicalDeriv (α : Sobolev.MultiIdx d k) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  Sobolev.iterPartialD (Sobolev.MultiIdx.dirs α.toFun).reverse u

/-- **Space `C^k(Ū)`.** A function of class `C^k(U)` whose derivatives `D^α u`, for
`|α| ≤ k`, are uniformly continuous on every bounded subset of `U`.
Evans Appendix A (Definition of function spaces, p. 702). -/
def CkBar (k : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContDiffOn ℝ k u U ∧ ∀ α : Sobolev.MultiIdx d k, ∀ B : Set (EuclideanSpace ℝ (Fin d)),
    Bornology.IsBounded B → UniformContinuousOn (classicalDeriv α u) (U ∩ B)

/-- A function uniformly continuous on the bounded pieces `U ∩ B` of `U` extends continuously
to the closure of `U`, and the extension agrees with the function on `U`. Evans's remark that
`D^α u` continuously extends to `Ū` for `u ∈ C^k(Ū)`. -/
theorem CkBar.exists_extension (_hU : IsOpen U) (h : CkBar k U u) (α : Sobolev.MultiIdx d k) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
      ContinuousOn g (closure U) ∧ Set.EqOn g (classicalDeriv α u) U := by
  set f := classicalDeriv α u with hf
  have hunif := h.2 α
  -- the limit of `f` along `U` exists at each point of `closure U`
  have hlim : ∀ x ∈ closure U, ∃ y, Tendsto f (𝓝[U] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[U] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
    have hball : Bornology.IsBounded (Metric.ball x 1) := Metric.isBounded_ball
    have hs : U ∩ Metric.ball x 1 ∈ 𝓝[U] x :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos))
    have hF : Cauchy (𝓝[U] x) :=
      (cauchy_nhds (a := x)).mono' inferInstance nhdsWithin_le_nhds
    refine cauchy_map_iff_exists_tendsto.1 ⟨inferInstance, ?_⟩
    have hprod : (𝓝[U] x) ×ˢ (𝓝[U] x) ≤ 𝓤 _ ⊓ 𝓟 ((U ∩ Metric.ball x 1) ×ˢ (U ∩ Metric.ball x 1)) :=
      le_inf hF.2 (by
        rw [← Filter.prod_principal_principal]
        exact Filter.prod_mono (le_principal_iff.2 hs) (le_principal_iff.2 hs))
    calc map f (𝓝[U] x) ×ˢ map f (𝓝[U] x)
        = map (Prod.map f f) ((𝓝[U] x) ×ˢ (𝓝[U] x)) := by
          rw [Filter.prod_map_map_eq]; rfl
      _ ≤ map (Prod.map f f) (𝓤 _ ⊓ 𝓟 ((U ∩ Metric.ball x 1) ×ˢ (U ∩ Metric.ball x 1))) :=
        Filter.map_mono hprod
      _ ≤ 𝓤 ℝ := hunif _ hball
  -- `f` is continuous on `U` because it is uniformly continuous on each `U ∩ ball x 1`
  have hcont : ContinuousOn f U := by
    intro x hx
    have hball : Bornology.IsBounded (Metric.ball x 1) := Metric.isBounded_ball
    have hs : Metric.ball x 1 ∈ 𝓝[U] x :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos)
    rw [← continuousWithinAt_inter' hs]
    exact (hunif _ hball).continuousOn x ⟨hx, Metric.mem_ball_self one_pos⟩
  exact ⟨extendFrom U f, continuousOn_extendFrom subset_rfl hlim,
    fun x hx => extendFrom_extends hcont x hx⟩

/-- **Space `L^p_loc(U)`.** The functions in `L^p(V)` for every `V ⊂⊂ U`, where `V ⊂⊂ U` means
that `V` has compact closure contained in `U`. Evans Appendix A (Definition of function spaces,
p. 702). -/
def MemLpLoc (p : ℝ≥0∞) (U : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ∀ V : Set (EuclideanSpace ℝ (Fin d)), IsCompact (closure V) → closure V ⊆ U →
    MemLp u p (volume.restrict V)

/-- On an open set the case `p = 1` of Evans's `L^p_loc(U)` is Mathlib's local integrability
on `U`. -/
theorem memLpLoc_one_iff (hU : IsOpen U) : MemLpLoc 1 U u ↔ LocallyIntegrableOn u U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  constructor
  · intro h K hKU hK
    have := h K (by rwa [hK.isClosed.closure_eq]) (by rwa [hK.isClosed.closure_eq])
    exact memLp_one_iff_integrable.1 this
  · intro h V hV hVU
    exact memLp_one_iff_integrable.2 ((h _ hVU hV).mono_set subset_closure)

/-- **Hölder's inequality.** For conjugate exponents `p`, `q` in `[1, ∞]` (the cases `p = 1`
and `p = ∞` are covered), `∫_U |u v| ≤ ‖u‖_{L^p(U)} ‖v‖_{L^q(U)}`.
Evans Appendix B (e) (Hölder's inequality, p. 706). -/
theorem integral_abs_mul_le {p q : ℝ≥0∞} [p.HolderConjugate q] {U : Set (EuclideanSpace ℝ (Fin d))}
    {u v : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u p (volume.restrict U)) (hv : MemLp v q (volume.restrict U)) :
    ∫ x in U, |u x * v x| ≤
      (eLpNorm u p (volume.restrict U)).toReal * (eLpNorm v q (volume.restrict U)).toReal := by
  have hle : eLpNorm (u • v) 1 (volume.restrict U) ≤
      eLpNorm u p (volume.restrict U) * eLpNorm v q (volume.restrict U) :=
    eLpNorm_smul_le_mul_eLpNorm hu.aestronglyMeasurable hv.aestronglyMeasurable
  have hint : Integrable (u • v) (volume.restrict U) := by
    have : MemLp (u • v) 1 (volume.restrict U) := hu.smul hv
    exact memLp_one_iff_integrable.1 this
  have heq : ∫ x in U, |u x * v x| = (eLpNorm (u • v) 1 (volume.restrict U)).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable]
    simp [Real.norm_eq_abs]
  rw [heq, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hu.eLpNorm_lt_top.ne hv.eLpNorm_lt_top.ne) hle

end EllipticPdes.Analysis
