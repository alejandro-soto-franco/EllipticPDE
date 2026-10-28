/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.WeakDerivMulti
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Sobolev space `W^{k,p}(U)`

The space `W^{k,p}(U)` is realised as the graph of the weak-derivative operator inside the
product `L^p(U)^N` over the multi-indices of order at most `k`. The product has the `ℓ^p`
norm (`PiLp p`), which for `p < ∞` is Evans's norm
`‖u‖ = (∑_{|α| ≤ k} ‖D^α u‖_p^p)^{1/p}`. Coordinate `α` of an element is the candidate
`α`-th weak derivative and coordinate `0` is the function. The weak-derivative relation is the
kernel of one continuous linear functional per multi-index and test function. The graph is a
closed submodule of a complete space and is therefore complete.

The functional pairs an `L^p` class against a smooth compactly supported function, which lies
in the conjugate `L^{p'}`. Hölder's inequality (`ContinuousLinearMap.lpPairing`) gives
continuity for every `p ∈ [1, ∞]` with no case split on `p = ∞`.

## Main declarations

* `EllipticPdes.Sobolev.WkpGraph`: the ambient product `L^p(U)^N`.
* `EllipticPdes.Sobolev.constraint`: the continuous functional cutting out the weak derivative.
* `EllipticPdes.Sobolev.Wkp`: the space `W^{k,p}(U)` as a submodule of `WkpGraph`.
* `EllipticPdes.Sobolev.isClosed_Wkp` and `EllipticPdes.Sobolev.Wkp.completeSpace`: `W^{k,p}(U)`
  is complete (Evans §5.2.3 Theorem 2, p. 262).
* `EllipticPdes.Sobolev.mem_Wkp_iff`: membership is the weak-derivative relation (Evans §5.2.2
  Definition, p. 258).
* `EllipticPdes.Sobolev.norm_Wkp_eq`: Evans's norm for `p < ∞` (Evans §5.2.2
  Definition, p. 259).
* `EllipticPdes.Sobolev.norm_Wkp_top_le` and `EllipticPdes.Sobolev.sum_le_card_mul_norm_Wkp_top`:
  the sup norm of the product is equivalent to Evans's sum of norms for `p = ∞`.
* `EllipticPdes.Sobolev.Wkp_zero_eq_top`: `W^{0,p}(U) = L^p(U)`.

## References

* [evans-2010] L. C. Evans: *Partial Differential Equations* (2nd ed.) §5.2.2 and §5.2.3.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace EllipticPdes.Sobolev

variable {d k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {U : Set (EuclideanSpace ℝ (Fin d))}
  {φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The ambient space of `W^{k,p}(U)`: one `L^p(U)` class for each multi-index of order at most
`k`, with the `ℓ^p` norm. Coordinate `α` is the candidate `α`-th weak derivative. -/
abbrev WkpGraph (d k : ℕ) (p : ℝ≥0∞) (U : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  WithLp p (MultiIdx d k → Lp ℝ p (volume.restrict U))

/-- An `L^p` class on `U` is locally integrable on `U` for Lebesgue measure, for `1 ≤ p`. -/
theorem locallyIntegrableOn_lp (f : Lp ℝ p (volume.restrict U)) : LocallyIntegrableOn f U :=
  locallyIntegrableOn_of_locallyIntegrable_restrict
    ((Lp.memLp f).locallyIntegrable (Fact.out : 1 ≤ p))

/-- Pairing with a continuous compactly supported function `g` is a continuous linear
functional on `L^p(U)`. The bound is Hölder's inequality against `g ∈ L^{p'}`, valid for every
`p ∈ [1, ∞]`. -/
def lpPair {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Lp ℝ p (volume.restrict U) →L[ℝ] ℝ :=
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (Fact.out : 1 ≤ p)
  have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume.restrict U) p (1 - p⁻¹)⁻¹).flip
    (((hg.memLp_of_hasCompactSupport (μ := volume) hc).restrict U).toLp g)

/-- The pairing functional is the integral of the product over `U`. -/
theorem lpPair_apply {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) (f : Lp ℝ p (volume.restrict U)) :
    lpPair (U := U) hg hc f = ∫ x in U, f x * g x := by
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (Fact.out : 1 ≤ p)
  have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := by simp [fact_iff]
  simp only [lpPair, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (((hg.memLp_of_hasCompactSupport (μ := volume) hc).restrict
    U))] with x hx
  rw [hx]

/-- **Weak-derivative constraint.** For a multi-index `α` and a test function `φ` of `U`,
the functional on `WkpGraph` sending `F` to
`∫_U F₀ D^α φ - (-1)^{|α|} ∫_U F_α φ`. Hölder's inequality makes it continuous, and its kernel
over all `α` and `φ` is `W^{k,p}(U)`. -/
def constraint (α : MultiIdx d k) (h : IsTestFn U φ) : WkpGraph d k p U →L[ℝ] ℝ :=
  let hD := h.iterPartialD (MultiIdx.dirs α.toFun)
  (lpPair hD.continuous hD.hasCompactSupport).comp
      (PiLp.proj p (fun _ : MultiIdx d k => Lp ℝ p (volume.restrict U)) MultiIdx.zero) -
    ((-1 : ℝ) ^ ∑ i, α.toFun i) •
      (lpPair h.continuous h.hasCompactSupport).comp
        (PiLp.proj p (fun _ : MultiIdx d k => Lp ℝ p (volume.restrict U)) α)

/-- The constraint functional as an explicit difference of integrals. -/
theorem constraint_apply (α : MultiIdx d k) (h : IsTestFn U φ) (F : WkpGraph d k p U) :
    constraint α h F = (∫ x in U, F MultiIdx.zero x * iterPartialD (MultiIdx.dirs α.toFun) φ x) -
      (-1 : ℝ) ^ (∑ i, α.toFun i) * ∫ x in U, F α x * φ x := by
  simp [constraint, lpPair_apply]

variable (d k p U) in
/-- **Sobolev space `W^{k,p}(U)`.** The functions of `L^p(U)` paired with all their weak
derivatives of order at most `k`, cut out of `WkpGraph` by the kernels of `constraint`. Evans
§5.2.2 Definition (p. 258). -/
def Wkp : Submodule ℝ (WkpGraph d k p U) :=
  ⨅ (α : MultiIdx d k) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (h : IsTestFn U φ),
    LinearMap.ker (constraint (p := p) α h : WkpGraph d k p U →ₗ[ℝ] ℝ)

/-- Membership in `Wkp` is the vanishing of every constraint. -/
theorem mem_Wkp_iff_constraint (F : WkpGraph d k p U) :
    F ∈ Wkp d k p U ↔ ∀ (α : MultiIdx d k) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
      (h : IsTestFn U φ), constraint α h F = 0 := by
  simp [Wkp, Submodule.mem_iInf]

/-- `W^{k,p}(U)` is an intersection of kernels of continuous functionals and is closed in
`WkpGraph`. -/
theorem isClosed_Wkp : IsClosed (Wkp d k p U : Set (WkpGraph d k p U)) := by
  simp only [Wkp, Submodule.coe_iInf]
  refine isClosed_iInter fun α => isClosed_iInter fun φ => isClosed_iInter fun h => ?_
  exact ContinuousLinearMap.isClosed_ker _

/-- **Completeness of `W^{k,p}(U)`.** It is a closed subspace of the complete space
`WkpGraph`. Evans §5.2.3 Theorem 2 (p. 262). -/
theorem Wkp.completeSpace : CompleteSpace (Wkp d k p U) :=
  isClosed_Wkp.completeSpace_coe

/-- `W^{k,p}(U)` is complete for every `p ∈ [1, ∞]`. -/
instance : CompleteSpace (Wkp d k p U) := Wkp.completeSpace

/-- **Membership in `W^{k,p}(U)` as weak derivatives.** A graph element lies in `W^{k,p}(U)`
exactly when coordinate `α` is the weak `α`-th derivative of coordinate `0` for every `α`.
Evans §5.2.2 Definition (p. 258). -/
theorem mem_Wkp_iff (F : WkpGraph d k p U) :
    F ∈ Wkp d k p U ↔
      ∀ α : MultiIdx d k, HasWeakDeriv U α.toFun (F MultiIdx.zero) (F α) := by
  rw [mem_Wkp_iff_constraint]
  refine forall_congr' fun α => ?_
  constructor
  · intro h
    refine ⟨locallyIntegrableOn_lp _, locallyIntegrableOn_lp _, fun φ hφ => ?_⟩
    have := h φ hφ
    rw [constraint_apply, sub_eq_zero] at this
    rw [this, MultiIdx.dirs_length]
  · intro h φ hφ
    rw [constraint_apply, sub_eq_zero]
    have := h.2.2 φ hφ
    rw [this, MultiIdx.dirs_length]

/-- **Evans's norm.** For `p < ∞` the norm on `W^{k,p}(U)` is
`(∑_{|α| ≤ k} ‖D^α u‖_p^p)^{1/p}`. Evans §5.2.2 Definition (p. 259). -/
theorem norm_Wkp_eq (hp : p ≠ ∞) (F : Wkp d k p U) :
    ‖F‖ = (∑ α, ‖(F : WkpGraph d k p U) α‖ ^ p.toReal) ^ (1 / p.toReal) :=
  PiLp.norm_eq_sum (ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp) _

/-- For `p = ∞` the norm of `W^{k,∞}(U)` is at most Evans's sum of the `L^∞` norms. -/
theorem norm_Wkp_top_le (F : Wkp d k ∞ U) : ‖F‖ ≤ ∑ α, ‖(F : WkpGraph d k ∞ U) α‖ := by
  change ‖(F : WkpGraph d k ∞ U)‖ ≤ _
  have : Nonempty (MultiIdx d k) := ⟨MultiIdx.zero⟩
  rw [PiLp.norm_eq_ciSup]
  exact ciSup_le fun α =>
    Finset.single_le_sum (f := fun α => ‖(F : WkpGraph d k ∞ U) α‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ α)

/-- For `p = ∞` Evans's sum of the `L^∞` norms is at most `#{α}` times the norm of
`W^{k,∞}(U)`. -/
theorem sum_le_card_mul_norm_Wkp_top (F : Wkp d k ∞ U) :
    ∑ α, ‖(F : WkpGraph d k ∞ U) α‖ ≤ Fintype.card (MultiIdx d k) * ‖F‖ := by
  calc ∑ α, ‖(F : WkpGraph d k ∞ U) α‖ ≤ ∑ _α : MultiIdx d k, ‖F‖ :=
        Finset.sum_le_sum fun α _ => PiLp.norm_apply_le (F : WkpGraph d k ∞ U) α
    _ = Fintype.card (MultiIdx d k) * ‖F‖ := by simp

/-- **Order zero.** `W^{0,p}(U)` is all of `L^p(U)`: the only multi-index is `0` and its
constraint is trivial. -/
theorem Wkp_zero_eq_top : Wkp d 0 p U = ⊤ := by
  refine eq_top_iff.2 fun F _ => ?_
  rw [mem_Wkp_iff_constraint]
  intro α φ h
  have hα : α = MultiIdx.zero := Subtype.ext (funext fun i =>
    Fin.ext (by have := (α.1 i).isLt; change (α.1 i).val = 0; omega))
  subst hα
  rw [constraint_apply, MultiIdx.dirs_zero]
  simp [MultiIdx.zero, MultiIdx.toFun]

end EllipticPdes.Sobolev
