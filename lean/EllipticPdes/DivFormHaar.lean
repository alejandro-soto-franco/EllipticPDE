/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.RellichHaar
public import EllipticPdes.Spectrum.DivForm
public import EllipticPdes.Existence.DivFormExistence
public import EllipticPdes.Poincare.GraphBounded

/-!
# Bounded-domain theorems for divergence-form operators and any additive Haar measure

`DivFormInstances` states the Fredholm and spectral theorems for the canonical volume. An
additive Haar measure `μ` is a positive multiple of `volume`, the embedding `H₀¹(Ω) ↪ L²(Ω)` stays
compact (`H1Graph.embL2_isCompact_haar`), and the abstract Fredholm and spectral layer needs
nothing else. Each theorem below is its `volume` namesake for an arbitrary additive Haar measure.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.fredholm_alternative_of_bounded_haar`
* `EllipticPdes.DivForm.FullEllipticOp.solvable_iff_orthogonal_transpose_of_bounded_haar`
* `EllipticPdes.DivForm.FullEllipticOp.existence_three_of_bounded_haar`
* `EllipticPdes.DivForm.FullEllipticOp.resolvent_bound_of_bounded_haar`
* `EllipticPdes.DivForm.FullEllipticOp.symmetric_spectral_of_bounded_haar`
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  (Op : FullEllipticOp μ) {Ω : Set E}

/-- **Fredholm alternative on a bounded set.** Either the homogeneous weak problem has a nonzero
solution, or `B[u, ·] = f` has a unique solution for every continuous functional `f`. -/
theorem fredholm_alternative_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    (∃ u : H1Graph.H01 μ Ω, u ≠ 0 ∧ ∀ v, Op.formOn Ω _ u v = 0) ∨
      ∀ f : StrongDual ℝ (H1Graph.H01 μ Ω), ∃! u, ∀ v, Op.formOn Ω _ u v = f v :=
  Op.fredholm_alternative Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb)

/-- If the homogeneous weak problem on a bounded set has only the trivial solution, then
`B[u, ·] = f` has a unique solution for every continuous functional `f`. -/
theorem fredholm_unique_imp_exists_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    (huniq : ∀ u : H1Graph.H01 μ Ω, (∀ v, Op.formOn Ω _ u v = 0) → u = 0)
    (f : StrongDual ℝ (H1Graph.H01 μ Ω)) :
    ∃! u, ∀ v, Op.formOn Ω _ u v = f v :=
  Op.fredholm_unique_imp_exists Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb) huniq f

/-- **Solvability criterion on a bounded set.** `B[u, ·] = f` has a solution exactly when `f`
annihilates every weak solution of the transpose problem. -/
theorem solvable_iff_orthogonal_transpose_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (f : StrongDual ℝ (H1Graph.H01 μ Ω)) :
    (∃ u, ∀ v, Op.formOn Ω _ u v = f v) ↔
      ∀ w, (∀ v, Op.formOn Ω _ v w = 0) → f w = 0 :=
  Op.solvable_iff_orthogonal_transpose Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb) f

/-- The `Σ`-membership characterisation on a bounded set. -/
theorem notMem_sigmaSet_iff_solvable_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      ∃! u : H1Graph.H01 μ Ω, ∀ v, Op.formOn Ω _ u v =
        lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ +
          ⟪f, H1Graph.embL2 μ Ω v⟫ :=
  Op.notMem_sigmaSet_iff_solvable Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb) lam

/-- **Existence III on a bounded set.** The exceptional set is countable, meets every
`(-∞, C]` in a finite set, and `lam` lies outside it exactly when the shifted weak problem is
uniquely solvable for every `f ∈ L²(Ω)`. -/
theorem existence_three_of_bounded_haar (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    (Op.sigmaSet Ω).Countable ∧ (∀ C : ℝ, (Op.sigmaSet Ω ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
        ∃! u : H1Graph.H01 μ Ω, ∀ v, Op.formOn Ω _ u v =
          lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ +
            ⟪f, H1Graph.embL2 μ Ω v⟫ :=
  Op.existence_three Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb)

/-- **Boundedness of the resolvent on a bounded set.** For `lam` outside the exceptional set, the
`L²` norm of a weak solution is bounded by a constant times the norm of the right-hand side. -/
theorem resolvent_bound_of_bounded_haar (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {lam : ℝ} (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℝ 2 (μ.restrict Ω)) (u : H1Graph.H01 μ Ω),
      (∀ v, Op.formOn Ω _ u v =
        lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ +
          ⟪f, H1Graph.embL2 μ Ω v⟫) →
        ‖H1Graph.embL2 μ Ω u‖ ≤ C * ‖f‖ :=
  Op.resolvent_bound Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb) hlam

/-- **Spectral theorem for symmetric operators on a bounded set.** For a self-adjoint coefficient
matrix, no drift and a nonnegative zeroth-order coefficient, the eigenspaces of the solution
operator span `L²(Ω)`. -/
theorem symmetric_spectral_of_bounded_haar [Nontrivial E] (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (ha : ∀ᵐ x ∂μ, (Op.a x).adjoint = Op.a x)
    (hb : ∀ᵐ x ∂μ, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) :
    ∃ hco : IsCoercive (Op.formOn Ω (H1Graph.H01 μ Ω)),
      (⨆ m : ℝ, Module.End.eigenspace
        (Variational.solOp (H1Graph.embL2 μ Ω) (Op.formOn Ω (H1Graph.H01 μ Ω)) hco :
          Module.End ℝ (Lp ℝ 2 (μ.restrict Ω))) m)ᗮ = ⊥ := by
  obtain ⟨CP, hCP, hP⟩ := H1Graph.poincare_H01_of_bounded (μ := μ) hΩb
  exact ⟨Op.isCoercive_formOn Ω hb hc hCP hP,
    Op.symmetric_spectral Ω (H1Graph.embL2_isCompact_haar μ hΩm hΩb) ha hb hc hCP hP⟩

end EllipticPdes.DivForm.FullEllipticOp
