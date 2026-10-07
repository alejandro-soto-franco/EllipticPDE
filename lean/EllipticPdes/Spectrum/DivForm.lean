/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.DivForm
public import EllipticPdes.Spectrum.GardingSigma
public import EllipticPdes.Spectrum.Spectrum

/-!
# Exceptional set and spectral theorem for divergence-form operators

Instances at `Op.gardingForm Ω` of the abstract results of `GardingSigma.lean` and
`Spectrum.lean`, each with the hypothesis `IsCompactOperator (H1Graph.embL2 μ Ω)`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.existence_three`: the exceptional set `sigmaSet` is
  countable, has finite slices, and characterises unique solvability of the shifted problem.
* `EllipticPdes.DivForm.FullEllipticOp.resolvent_bound`: the resolvent is bounded off `sigmaSet`.
* `EllipticPdes.DivForm.FullEllipticOp.symmetric_spectral`: the eigenfunctions of the solution
  operator of a symmetric operator span `L²(Ω)`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
  (Op : FullEllipticOp μ) (Ω : Set E)

/-- The exceptional set of the operator on `Ω`. -/
abbrev sigmaSet : Set ℝ := (Op.gardingForm Ω).sigmaSet

/-- `lam` lies outside the exceptional set exactly when `B[u, ·] = lam ⟪u, ·⟫ + f` has a unique
solution for every `f`. -/
theorem notMem_sigmaSet_iff_solvable (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      ∃! u : H1Graph.H01 μ Ω, ∀ v, Op.formOn Ω _ u v =
        lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ + ⟪f, H1Graph.embL2 μ Ω v⟫ :=
  (Op.gardingForm Ω).existence_three (Op.opK_isCompact Ω hK) |>.2.2 lam

/-- **Existence III** (Evans §6.2.3, Theorem 5). The exceptional set is countable, meets every
`(-∞, C]` in a finite set, and `lam` lies outside it exactly when the shifted weak problem is
uniquely solvable for every `f ∈ L²(Ω)`. -/
theorem existence_three (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) :
    (Op.sigmaSet Ω).Countable ∧ (∀ C : ℝ, (Op.sigmaSet Ω ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
        ∃! u : H1Graph.H01 μ Ω, ∀ v, Op.formOn Ω _ u v =
          lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ + ⟪f, H1Graph.embL2 μ Ω v⟫ :=
  (Op.gardingForm Ω).existence_three (Op.opK_isCompact Ω hK)

/-- **Boundedness of the resolvent.** For `lam` outside the exceptional set, the `L²` norm of a
weak solution is bounded by a constant times the norm of the right-hand side. -/
theorem resolvent_bound (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℝ 2 (μ.restrict Ω)) (u : H1Graph.H01 μ Ω),
      (∀ v, Op.formOn Ω _ u v =
        lam * ⟪H1Graph.embL2 μ Ω u, H1Graph.embL2 μ Ω v⟫ + ⟪f, H1Graph.embL2 μ Ω v⟫) →
        ‖H1Graph.embL2 μ Ω u‖ ≤ C * ‖f‖ :=
  (Op.gardingForm Ω).resolvent_bound (Op.opK_isCompact Ω hK) hlam

/-- With no drift, a nonnegative zeroth-order coefficient and a Poincaré inequality, the full
form on `H₀¹(Ω)` is coercive. -/
lemma isCoercive_formOn (hb : ∀ᵐ x ∂μ, Op.b x = 0) (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x)
    {CP : ℝ} (hCP : 0 ≤ CP)
    (hP : ∀ U ∈ H1Graph.H01 μ Ω, ‖H1Graph.fnL U‖ ^ 2 ≤ CP * ‖H1Graph.gradL U‖ ^ 2) :
    IsCoercive (Op.formOn Ω (H1Graph.H01 μ Ω)) :=
  ⟨Op.lam / (CP + 1), div_pos Op.lam_pos (by linarith),
    Op.form_coercive_of_poincare (ae_restrict_of_ae hb) hc hCP hP⟩

/-- **Spectral theorem for symmetric operators.** For a self-adjoint coefficient matrix, no
drift, a nonnegative zeroth-order coefficient and a Poincaré inequality on `H₀¹(Ω)`, the
eigenspaces of the solution operator span `L²(Ω)`. -/
theorem symmetric_spectral (hK : IsCompactOperator (H1Graph.embL2 μ Ω))
    (ha : ∀ᵐ x ∂μ, (Op.a x).adjoint = Op.a x) (hb : ∀ᵐ x ∂μ, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) {CP : ℝ} (hCP : 0 ≤ CP)
    (hP : ∀ U ∈ H1Graph.H01 μ Ω, ‖H1Graph.fnL U‖ ^ 2 ≤ CP * ‖H1Graph.gradL U‖ ^ 2) :
    (⨆ m : ℝ, Module.End.eigenspace
      (Variational.solOp (H1Graph.embL2 μ Ω) (Op.formOn Ω (H1Graph.H01 μ Ω))
        (Op.isCoercive_formOn Ω hb hc hCP hP) : Module.End ℝ (Lp ℝ 2 (μ.restrict Ω))) m)ᗮ =
      ⊥ :=
  Variational.orthogonal_iSup_eigenspace_solOp (Op.isCoercive_formOn Ω hb hc hCP hP)
    (fun U V => by
      simpa only [formOn_apply] using Op.form_symm (Ω := Ω) ha hb (U : H1Graph μ Ω) V) hK

end EllipticPdes.DivForm.FullEllipticOp
