/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Wkp0
public import EllipticPdes.Sobolev.Basic

/-!
# Graph-space bridges for `W^{1,2}(U)` and `W_0^{1,2}(U)`

The general spaces `Wkp d 1 2 U` and `W0kp d 1 2 U` are submodules of the product indexed by
the multi-indices of order at most one. The spaces `W12 U` and `H01 U` are submodules of
`H1amb U`. That space is indexed by `Fin (d + 1)`. Coordinate `0` is the function and
coordinate `i.succ` is the `i`-th weak partial. The multi-index `0` corresponds to `0` and
the multi-index `Pi.single i 1` to `i.succ`. Reindexing along this bijection is a linear isometric
equivalence that matches the two pairs of submodules.

## Main declarations

* `EllipticPdes.Sobolev.MultiIdx.oneEquiv`: the bijection `MultiIdx d 1 ≃ Fin (d + 1)`.
* `EllipticPdes.Sobolev.toH1amb`: the reindexing `WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U`.
* `EllipticPdes.Sobolev.norm_toH1amb`: the reindexing preserves the norm.
* `EllipticPdes.Sobolev.mem_Wkp_one_two_iff`: it maps `W^{1,2}(U)` onto `W12 U`.
* `EllipticPdes.Sobolev.mem_W0kp_one_two_iff`: it maps `W_0^{1,2}(U)` onto `H01 U`.

## References

* [evans-2010] L. C. Evans: *Partial Differential Equations* (2nd ed.) §5.2.2 Definition
  (pp. 258–259).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} {φ : EuclideanSpace ℝ (Fin d) → ℝ}

/-! ### Multi-indices of order at most one -/

namespace MultiIdx

/-- The zero multi-index differentiates in no direction. -/
theorem dirs_zero : dirs (zero (d := d) (k := 1)).toFun = [] := by
  simp [dirs, zero, toFun]

/-- The multi-index of order one in direction `i`. -/
def single (i : Fin d) : MultiIdx d 1 :=
  ⟨Pi.single i 1, by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp⟩

/-- The exponents of `single i` are `Pi.single i 1`. -/
theorem toFun_single (i : Fin d) : (single i).toFun = Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [single, toFun]
  · simp [single, toFun, Pi.single_eq_of_ne hj]

/-- A multi-index of order at most one is zero or a coordinate multi-index. -/
theorem eq_zero_or_single (α : MultiIdx d 1) : α = zero ∨ ∃ i, α = single i := by
  by_cases h : ∀ j, (α.1 j : ℕ) = 0
  · exact Or.inl (Subtype.ext (funext fun j => Fin.ext (h j)))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    right
    refine ⟨i, Subtype.ext (funext fun j => ?_)⟩
    have hsum := α.2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsum
    have hi1 : (α.1 i : ℕ) = 1 := by
      have := (α.1 i).isLt
      omega
    have hrest : ∑ j ∈ Finset.univ.erase i, (α.1 j : ℕ) = 0 := by omega
    by_cases hj : j = i
    · subst hj
      exact Fin.ext (by simpa [single] using hi1)
    · have := (Finset.sum_eq_zero_iff.1 hrest) j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      exact Fin.ext (by simpa [single, Pi.single_eq_of_ne hj] using this)

/-- The inverse of `oneEquiv`: `0 ↦ 0` and `i.succ ↦ Pi.single i 1`. -/
def ofFin : Fin (d + 1) → MultiIdx d 1 :=
  Fin.cons zero single

/-- `ofFin` is a bijection. -/
theorem ofFin_bijective : Function.Bijective (ofFin : Fin (d + 1) → MultiIdx d 1) := by
  have hz : ∀ i : Fin d, zero ≠ single (d := d) i := fun i h => by
    have := congrFun (congrArg Subtype.val h) i
    simp [zero, single] at this
  have hs : ∀ i j : Fin d, single (d := d) i = single j → i = j := fun i j h => by
    have := congrFun (congrArg Subtype.val h) i
    by_contra hij
    simp [single, Pi.single_eq_of_ne hij] at this
  constructor
  · intro a b hab
    induction a using Fin.cases <;> induction b using Fin.cases <;>
      simp only [ofFin, Fin.cons_zero, Fin.cons_succ] at hab
    · rfl
    · exact absurd hab (hz _)
    · exact absurd hab.symm (hz _)
    · rw [hs _ _ hab]
  · intro α
    rcases eq_zero_or_single α with rfl | ⟨i, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨i.succ, rfl⟩

/-- **Reindexing of order-one multi-indices.** The zero index goes to `0` and `Pi.single i 1`
to `i.succ`. -/
def oneEquiv : MultiIdx d 1 ≃ Fin (d + 1) :=
  (Equiv.ofBijective ofFin ofFin_bijective).symm

/-- The inverse of `oneEquiv` sends `0` to the zero multi-index. -/
theorem oneEquiv_symm_zero : (oneEquiv (d := d)).symm 0 = zero := rfl

/-- The inverse of `oneEquiv` sends `i.succ` to `Pi.single i 1`. -/
theorem oneEquiv_symm_succ (i : Fin d) : (oneEquiv (d := d)).symm i.succ = single i := rfl

end MultiIdx

/-! ### Reindexing -/

/-- **Reindexing to the ambient space.** Coordinate `0` of the image is the function and
coordinate `i.succ` the entry of the multi-index `Pi.single i 1`. -/
def toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (L2D U) MultiIdx.oneEquiv).toLinearEquiv

/-- Coordinate `j` of `toH1amb F` is the entry of `F` at the multi-index over `j`. -/
theorem toH1amb_apply (F : WkpGraph d 1 2 U) (j : Fin (d + 1)) :
    toH1amb F j = F (MultiIdx.oneEquiv.symm j) := rfl

/-- **Norm preservation.** Reindexing preserves the norm. -/
theorem norm_toH1amb (F : WkpGraph d 1 2 U) : ‖toH1amb F‖ = ‖F‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (L2D U) MultiIdx.oneEquiv).norm_map F

/-! ### Membership in `W^{1,2}(U)` -/

/-- The inner product against the class of the `i`-th partial of a test function. -/
private theorem inner_partialCls (h : IsTestFn U φ) (i : Fin d) (u : L2D U) :
    ⟪h.partialCls i, u⟫_ℝ = ∫ x in U, u x * partialD i φ x := by
  rw [L2.real_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_partialCls i] with x hx
  rw [hx, mul_comm]

/-- The inner product against the class of a test function. -/
private theorem inner_testCls (h : IsTestFn U φ) (v : L2D U) :
    ⟪h.testCls, v⟫_ℝ = ∫ x in U, v x * φ x := by
  rw [L2.real_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_testCls] with x hx
  rw [hx, mul_comm]

/-- **`W^{1,2}(U)` through the reindexing.** A graph element lies in `W^{1,2}(U)` exactly
when its reindexing satisfies the constraints that define `W12 U`. -/
theorem mem_Wkp_one_two_iff (F : WkpGraph d 1 2 U) :
    F ∈ Wkp d 1 2 U ↔ toH1amb F ∈ W12 U := by
  rw [mem_Wkp_iff, mem_W12_iff]
  constructor
  · intro h φ hφ i
    have hw := (hasWeakDeriv_single_iff_integral.1
      (MultiIdx.toFun_single i ▸ h (MultiIdx.single i))).2.2 φ hφ
    rw [inner_partialCls, inner_testCls, toH1amb_apply, toH1amb_apply,
      MultiIdx.oneEquiv_symm_zero, MultiIdx.oneEquiv_symm_succ]
    linarith
  · intro h α
    rcases MultiIdx.eq_zero_or_single α with rfl | ⟨i, rfl⟩
    · refine ⟨locallyIntegrableOn_lp _, locallyIntegrableOn_lp _, fun φ _ => ?_⟩
      rw [MultiIdx.dirs_zero]
      simp
    · rw [MultiIdx.toFun_single, hasWeakDeriv_single_iff_integral]
      refine ⟨locallyIntegrableOn_lp _, locallyIntegrableOn_lp _, fun φ hφ => ?_⟩
      have := h φ hφ i
      rw [inner_partialCls, inner_testCls, toH1amb_apply, toH1amb_apply,
        MultiIdx.oneEquiv_symm_zero, MultiIdx.oneEquiv_symm_succ] at this
      linarith

/-! ### Membership in `W_0^{1,2}(U)` -/

/-- The reindexing sends the graph of a test function to the ambient graph. -/
theorem toH1amb_testGraph (h : IsTestFn U φ) :
    toH1amb (testGraph h : WkpGraph d 1 2 U) = h.testGraph := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [toH1amb_apply, IsTestFn.testGraph_zero, MultiIdx.oneEquiv_symm_zero, testGraph_apply]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by
      rw [MultiIdx.dirs_zero]; rfl))
  · rw [toH1amb_apply, IsTestFn.testGraph_succ, MultiIdx.oneEquiv_symm_succ, testGraph_apply]
    refine MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq ?_)
    rw [MultiIdx.toFun_single, MultiIdx.dirs_single]
    rfl

/-- **`W_0^{1,2}(U)` through the reindexing.** A graph element lies in `W_0^{1,2}(U)` exactly
when its reindexing lies in `H01 U`. -/
theorem mem_W0kp_one_two_iff (F : WkpGraph d 1 2 U) :
    F ∈ W0kp d 1 2 U ↔ toH1amb F ∈ H01 U := by
  set e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ (L2D U) (MultiIdx.oneEquiv (d := d))
  have himg : (toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U) '' wkpTestGraphs d 1 2 U =
      testGraphSet U := by
    ext G
    constructor
    · rintro ⟨_, ⟨φ, h, rfl⟩, rfl⟩
      exact ⟨φ, h, toH1amb_testGraph h⟩
    · rintro ⟨φ, h, rfl⟩
      exact ⟨testGraph h, ⟨φ, h, rfl⟩, toH1amb_testGraph h⟩
  have hspan : (toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U) ''
      (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U)) =
      (Submodule.span ℝ (testGraphSet U) : Set (H1amb U)) := by
    have := Submodule.map_span (toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U).toLinearMap
      (wkpTestGraphs d 1 2 U)
    have e2 : ((toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U).toLinearMap :
        WkpGraph d 1 2 U → H1amb U) '' wkpTestGraphs d 1 2 U = testGraphSet U := himg
    rw [e2] at this
    exact congrArg (fun S : Submodule ℝ (H1amb U) => (S : Set (H1amb U))) this
  rw [← SetLike.mem_coe, ← SetLike.mem_coe, W0kp, H01, Submodule.topologicalClosure_coe,
    Submodule.topologicalClosure_coe, ← hspan]
  have hcl := e.toHomeomorph.image_closure
    (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U))
  have hF : toH1amb F ∈ closure ((toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U) ''
      (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U))) ↔
        F ∈ closure (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U)) := by
    have : closure ((toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U) ''
        (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U))) =
        (toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U) '' closure
          (Submodule.span ℝ (wkpTestGraphs d 1 2 U) : Set (WkpGraph d 1 2 U)) := hcl.symm
    rw [this]
    exact (toH1amb : WkpGraph d 1 2 U ≃ₗ[ℝ] H1amb U).injective.mem_set_image
  exact hF.symm

end EllipticPdes.Sobolev
