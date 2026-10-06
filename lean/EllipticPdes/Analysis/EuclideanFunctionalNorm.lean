/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Norm of a functional on Euclidean space in standard coordinates

A continuous linear functional `L` on `EuclideanSpace ℝ (Fin n)` has squared norm equal to the
sum of the squares of its values on the standard basis vectors: `‖L‖² = ∑ i, (L (single i 1))²`.
Through the Fréchet-Riesz representation, `L (single i 1)` is the `i`-th coordinate of the Riesz
vector, and the identity is Parseval for that vector.

Applied to `L = fderiv ℝ φ x`, this expresses the squared gradient norm `‖fderiv ℝ φ x‖²` as the
sum of squared partial derivatives `∑ i, (∂ᵢ φ x)²`, the form in which the gradient `L²` norm of
`MeasureTheory.integral_sq_sub_translation_le` meets a Sobolev `H¹` gradient bound.
-/

@[expose] public section

open scoped RealInnerProductSpace
open InnerProductSpace

namespace EllipticPdes.Analysis

/-- The squared norm of a functional on a finite-dimensional inner product space is the sum of
the squares of its values on an orthonormal basis: Parseval for the Riesz vector of the
functional. -/
theorem norm_sq_dual_eq_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (b : OrthonormalBasis ι ℝ E)
    (L : StrongDual ℝ E) : ‖L‖ ^ 2 = ∑ i, (L (b i)) ^ 2 := by
  set v : E := (toDual ℝ E).symm L
  have hnorm : ‖L‖ = ‖v‖ := ((toDual ℝ E).symm.norm_map L).symm
  have happ : ∀ i, L (b i) = ⟪b i, v⟫ := fun i => by
    rw [real_inner_comm, toDual_symm_apply]
  rw [hnorm, ← b.sum_sq_norm_inner_right v]
  exact Finset.sum_congr rfl fun i _ => by rw [happ, Real.norm_eq_abs, sq_abs]

end EllipticPdes.Analysis

/-- The squared operator norm of a functional on Euclidean space is the sum of the squares of its
values on the standard basis vectors. -/
theorem norm_sq_clm_eq_sum_apply_single {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, (L (EuclideanSpace.single i 1)) ^ 2 := by
  simpa using EllipticPdes.Analysis.norm_sq_dual_eq_sum (EuclideanSpace.basisFun (Fin n) ℝ) L
