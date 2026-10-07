/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.GardingForm
public import EllipticPdes.Form.DivFormGarding

/-!
# Fredholm theory for divergence-form operators on a general inner product space

For a `DivForm.FullEllipticOp μ` on a finite-dimensional real inner product space `E`, the full
form on `H₀¹(Ω)` is a `GardingForm` over `L²(Ω)` (`gardingForm`): its Gårding inequality is
`FullEllipticOp.garding_embL2`. Every theorem of the abstract Fredholm layer is therefore an
instance, with the Rellich-Kondrachov hypothesis `IsCompactOperator (H1Graph.embL2 μ Ω)`.

## Main declarations

* `EllipticPdes.DivForm.FullEllipticOp.gardingForm`: the operator as a Gårding form.
* `EllipticPdes.DivForm.FullEllipticOp.fredholm_alternative`: the Fredholm alternative.
* `EllipticPdes.DivForm.FullEllipticOp.solvable_iff_orthogonal_transpose`: the solvability
  criterion against the weak solutions of the transpose problem.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.DivForm.FullEllipticOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- The operator as a Gårding form on `H₀¹(Ω)` over `L²(Ω)`: the form is `Op.formOn`, the
embedding is `H1Graph.embL2`, and the Gårding inequality has constants `λ / 2` and `gardingγ`. -/
def gardingForm (Op : FullEllipticOp μ) (Ω : Set E) :
    GardingForm (H1Graph.H01 μ Ω) (Lp ℝ 2 (μ.restrict Ω)) where
  form := Op.formOn Ω (H1Graph.H01 μ Ω)
  emb := H1Graph.embL2 μ Ω
  β := Op.lam / 2
  γ := Op.gardingγ
  β_pos := half_pos Op.lam_pos
  γ_pos := Op.gardingγ_pos
  garding := Op.garding_embL2 Ω

variable (Op : FullEllipticOp μ) (Ω : Set E)

/-- The Riesz theory of the compact part of the operator follows from the compactness of
`H₀¹(Ω) ↪ L²(Ω)`. -/
lemma opK_isCompact (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) :
    IsCompactOperator (Op.gardingForm Ω).opK :=
  (Op.gardingForm Ω).opK_isCompact hK

/-- **Fredholm alternative** (Evans §6.2.3, Theorem 4). If `H₀¹(Ω) ↪ L²(Ω)` is compact, either
the homogeneous weak problem has a nonzero solution, or `B[u, ·] = f` has a unique solution for
every continuous functional `f`. -/
theorem fredholm_alternative (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) :
    (∃ u : H1Graph.H01 μ Ω, u ≠ 0 ∧ ∀ v, Op.formOn Ω _ u v = 0) ∨
      ∀ f : StrongDual ℝ (H1Graph.H01 μ Ω), ∃! u, ∀ v, Op.formOn Ω _ u v = f v :=
  (Op.gardingForm Ω).fredholm_alternative (Op.opK_isCompact Ω hK)

/-- If the homogeneous weak problem has only the trivial solution, then `B[u, ·] = f` has a
unique solution for every continuous functional `f`. -/
theorem fredholm_unique_imp_exists (hK : IsCompactOperator (H1Graph.embL2 μ Ω))
    (huniq : ∀ u : H1Graph.H01 μ Ω, (∀ v, Op.formOn Ω _ u v = 0) → u = 0)
    (f : StrongDual ℝ (H1Graph.H01 μ Ω)) :
    ∃! u, ∀ v, Op.formOn Ω _ u v = f v :=
  (Op.gardingForm Ω).fredholm_unique_imp_exists (Op.opK_isCompact Ω hK) huniq f

/-- The weak solutions of the homogeneous problem form a finite-dimensional space. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) :
    FiniteDimensional ℝ (Op.gardingForm Ω).solSpace :=
  (Op.gardingForm Ω).finiteDimensional_solSpace (Op.opK_isCompact Ω hK)

/-- Membership in the space of weak solutions of the transpose problem `B[v, u] = 0`. -/
lemma mem_solSpaceStar_iff (u : H1Graph.H01 μ Ω) :
    u ∈ (Op.gardingForm Ω).solSpaceStar ↔ ∀ v, Op.formOn Ω _ v u = 0 :=
  (Op.gardingForm Ω).mem_solSpaceStar_iff u

/-- **Solvability criterion** (Evans §6.2.3, Theorem 4(iii)). `B[u, ·] = f` has a solution
exactly when `f` annihilates every weak solution of the transpose problem. -/
theorem solvable_iff_orthogonal_transpose (hK : IsCompactOperator (H1Graph.embL2 μ Ω))
    (f : StrongDual ℝ (H1Graph.H01 μ Ω)) :
    (∃ u, ∀ v, Op.formOn Ω _ u v = f v) ↔
      ∀ w, (∀ v, Op.formOn Ω _ v w = 0) → f w = 0 := by
  refine ((Op.gardingForm Ω).solvable_iff_orthogonal_solSpaceStar (Op.opK_isCompact Ω hK)
    f).trans ?_
  exact ⟨fun h w hw => h w ((Op.mem_solSpaceStar_iff Ω w).mpr hw),
    fun h w hw => h w ((Op.mem_solSpaceStar_iff Ω w).mp hw)⟩

/-- The homogeneous and the transpose problem have weak-solution spaces of equal dimension. -/
theorem finrank_solSpaceStar_eq (hK : IsCompactOperator (H1Graph.embL2 μ Ω)) :
    Module.finrank ℝ (Op.gardingForm Ω).solSpaceStar =
      Module.finrank ℝ (Op.gardingForm Ω).solSpace :=
  (Op.gardingForm Ω).finrank_solSpaceStar_eq_finrank_solSpace (Op.opK_isCompact Ω hK)

end EllipticPdes.DivForm.FullEllipticOp
