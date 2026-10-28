/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Bounded operators and reflexivity

Evans defines a linear operator to be bounded when the supremum of `‖A u‖` over the closed
unit ball is finite, the dual of a real Banach space as its bounded linear functionals, and a
space to be reflexive when the canonical map into the double dual is onto. This file states
each notion as Evans does and proves the characterising theorem against Mathlib's `StrongDual`
and `NormedSpace.inclusionInDoubleDual`.

## Main declarations

* `EllipticPdes.Analysis.IsBoundedLinear`: the supremum over the unit ball is finite.
* `EllipticPdes.Analysis.isBoundedLinear_iff_continuous`: bounded and continuous coincide.
* `EllipticPdes.Analysis.IsBoundedLinear.sSup_eq_opNorm`: a continuous linear map is bounded and
  the supremum is its operator norm.
* `EllipticPdes.Analysis.exists_dual_iff`: a linear functional is a dual element iff bounded.
* `EllipticPdes.Analysis.riesz_representation`: Riesz representation on a Hilbert space.
* `EllipticPdes.Analysis.IsReflexive`: the canonical map into the double dual is onto.
* `EllipticPdes.Analysis.isReflexive_iff`: the pointwise form of reflexivity.
* `EllipticPdes.Analysis.isReflexive_of_hilbert`: a Hilbert space is reflexive.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), Appendix D.3: bounded linear
operators (p. 721) and the dual space with its Riesz theorem (p. 722).
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace EllipticPdes.Analysis

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Bounded linear operator.** `A` is bounded when `sup {‖A u‖ : ‖u‖ ≤ 1}` is finite. The
definition states this as the image of the closed unit ball under `‖A ·‖` being bounded above.
Evans Appendix D.3 (Definition of a bounded linear operator, p. 721). -/
def IsBoundedLinear (A : X →ₗ[ℝ] Y) : Prop :=
  BddAbove ((fun u => ‖A u‖) '' Metric.closedBall (0 : X) 1)

/-- A linear operator is bounded on the unit ball iff it is continuous. Evans checks that a
bounded operator is continuous (Appendix D.3, p. 721), and the converse is proved here. -/
theorem isBoundedLinear_iff_continuous (A : X →ₗ[ℝ] Y) :
    IsBoundedLinear A ↔ Continuous A := by
  constructor
  · rintro ⟨C, hC⟩
    refine (LinearMap.mkContinuous A C fun x => ?_).continuous
    by_cases hx : x = 0
    · subst hx
      have h0 : ‖A 0‖ ≤ C := hC ⟨0, by simp, rfl⟩
      simp
    · have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hmem : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : X) 1 := by
        simp [norm_smul, hpos.ne']
      have h := hC ⟨_, hmem, rfl⟩
      simp only [map_smul, norm_smul, norm_inv, norm_norm] at h
      have h' : ‖A x‖ ≤ C * ‖x‖ := by
        have := mul_le_mul_of_nonneg_left h hpos.le
        rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
      exact h'
  · intro h
    let B : X →L[ℝ] Y := ⟨A, h⟩
    refine ⟨‖B‖, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    calc ‖A u‖ = ‖B u‖ := rfl
      _ ≤ ‖B‖ * ‖u‖ := B.le_opNorm u
      _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left hu' (norm_nonneg _)
      _ = ‖B‖ := mul_one _

/-- A continuous linear map is a bounded linear operator, and the supremum of `‖A u‖` over the
closed unit ball is its operator norm. Evans Appendix D.3 (Definition of a bounded linear
operator, p. 721). -/
theorem IsBoundedLinear.sSup_eq_opNorm (A : X →L[ℝ] Y) :
    IsBoundedLinear (A : X →ₗ[ℝ] Y) ∧
      sSup ((fun u => ‖A u‖) '' Metric.closedBall (0 : X) 1) = ‖A‖ :=
  ⟨(isBoundedLinear_iff_continuous _).2 A.continuous, A.sSup_unitClosedBall_eq_norm⟩

/-- A linear functional is an element of the dual space iff it is bounded. Evans Appendix D.3
(Definition of the dual space, p. 722). -/
theorem exists_dual_iff (f : X →ₗ[ℝ] ℝ) :
    (∃ g : StrongDual ℝ X, ⇑g = ⇑f) ↔ IsBoundedLinear f := by
  rw [isBoundedLinear_iff_continuous]
  constructor
  · rintro ⟨g, hg⟩
    have : f = g := LinearMap.ext fun x => (congrFun hg x).symm
    rw [this]
    exact g.continuous
  · intro h
    exact ⟨⟨f, h⟩, rfl⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Riesz representation.** On a real Hilbert space every bounded linear functional is the
inner product against a unique vector, and the assignment is a linear equivalence from the dual
space onto `H`. Evans Appendix D.3 (Theorem 2, p. 722). -/
theorem riesz_representation [CompleteSpace H] :
    (∀ f : StrongDual ℝ H, ∃! u : H, ∀ v, f v = ⟪u, v⟫_ℝ) ∧
      ∃ e : StrongDual ℝ H ≃ₗ[ℝ] H, ∀ f v, f v = ⟪e f, v⟫_ℝ := by
  have key : ∀ f : StrongDual ℝ H, ∀ v, f v = ⟪(InnerProductSpace.toDual ℝ H).symm f, v⟫_ℝ :=
    fun f v => (InnerProductSpace.toDual_symm_apply).symm
  refine ⟨fun f => ⟨(InnerProductSpace.toDual ℝ H).symm f, key f, fun u hu => ?_⟩, ?_⟩
  · exact ext_inner_right ℝ fun v => by rw [← hu v, key f v]
  · refine ⟨{ toFun := fun f => (InnerProductSpace.toDual ℝ H).symm f
              map_add' := fun f g => map_add _ f g
              map_smul' := fun c f => by simp
              invFun := fun u => InnerProductSpace.toDual ℝ H u
              left_inv := fun f => by simp
              right_inv := fun u => by simp }, key⟩

/-- **Reflexive space.** The canonical map of `X` into its double dual is onto. Evans
Appendix D.3 (Definition of reflexive, p. 722). -/
def IsReflexive (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- Reflexivity in pointwise form: every bounded functional `φ` on the dual space is evaluation
at a point `u` of `X`. Evans Appendix D.3 (Definition of reflexive, p. 722). -/
theorem isReflexive_iff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    IsReflexive X ↔ ∀ φ : StrongDual ℝ (StrongDual ℝ X), ∃ u : X, ∀ f, φ f = f u := by
  constructor
  · intro h φ
    obtain ⟨u, hu⟩ := h φ
    exact ⟨u, fun f => by rw [← hu]; rfl⟩
  · intro h φ
    obtain ⟨u, hu⟩ := h φ
    exact ⟨u, ContinuousLinearMap.ext fun f => (hu f).symm⟩

/-- A real Hilbert space is reflexive. -/
theorem isReflexive_of_hilbert [CompleteSpace H] : IsReflexive H := by
  rw [isReflexive_iff]
  intro φ
  obtain ⟨u, hu, -⟩ := (riesz_representation (H := H)).1 (φ.comp (innerSL ℝ))
  refine ⟨u, fun f => ?_⟩
  set w := (InnerProductSpace.toDual ℝ H).symm f with hw
  have hf : f = innerSL ℝ w := by
    ext v
    rw [innerSL_apply_apply, ← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := f)]
  calc φ f = φ (innerSL ℝ w) := by rw [← hf]
    _ = ⟪u, w⟫_ℝ := hu w
    _ = f u := by rw [real_inner_comm, hf]; rfl

end EllipticPdes.Analysis
