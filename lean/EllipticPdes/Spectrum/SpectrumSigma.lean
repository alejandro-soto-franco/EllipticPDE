/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.FredholmComplete
public import EllipticPdes.Spectrum.GardingSigma

/-!
# Existence III for the elliptic problem

The Euclidean instance of the abstract exceptional set (`GardingSigma.lean`): the set
`Σ = {λ : γ/(γ+λ) is an eigenvalue of opK}` of `Op.gardingForm Ω` is countable with finite
intersections with every `Set.Iic C`, and `λ ∉ Σ` holds exactly when the weak problem
`Lu = λu + f` is uniquely solvable for every right-hand side. The `∫ f · v₀` shapes of the
statements come from `L2.real_inner_eq_integral`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

namespace FullEllipticOp

variable {d : ℕ} (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- **Set `Σ` of Existence III**: the real `λ` for which `γ/(γ+λ)` is an
eigenvalue of the compact part `opK` of the reduction, equivalently (see
`notMem_sigmaSet_iff_solvable`), the `λ` for which the weak problem `Lu = λu + f`
fails to be uniquely solvable for every right-hand side. -/
def sigmaSet : Set ℝ := (Op.gardingForm Ω).sigmaSet

/-- The `λ`-shifted weak problem for a functional is uniquely solvable off `Σ`, and conversely:
`λ ∉ Σ` exactly when `B[u,v] = λ⟨u₀,v₀⟩ + f(v)` is uniquely solvable for every `f`. -/
theorem notMem_sigmaSet_iff_solvable (hK : IsCompactOperator (Op.opK Ω)) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω
      ↔ ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
          Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v :=
  (Op.gardingForm Ω).notMem_sigmaSet_iff_solvable hK lam

/-- Bounded-above slices of `Σ` are finite. -/
theorem sigmaSet_inter_Iic_finite (hK : IsCompactOperator (Op.opK Ω)) (C : ℝ) :
    (Op.sigmaSet Ω ∩ Set.Iic C).Finite :=
  (Op.gardingForm Ω).sigmaSet_inter_Iic_finite hK C

/-- The weak problem with an `L²` right-hand side, in the abstract shape, is the integral
form. -/
private lemma gardingForm_iff {lam : ℝ} (f : L2D Ω) (u v : H01 Ω) :
    (Op.gardingForm Ω).form u v = lam * ⟪(Op.gardingForm Ω).emb u, (Op.gardingForm Ω).emb v⟫
        + ⟪f, (Op.gardingForm Ω).emb v⟫ ↔
      Op.fullBilin Ω u v = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
        + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) := by
  rw [← L2.real_inner_eq_integral]
  rfl

/-- **Existence III.** There is a set `Σ ⊆ ℝ`, countable and with
finite intersection with every `(-∞, C]` (so an infinite `Σ` is a nondecreasing
sequence diverging to `+∞`), such that for every `λ ∉ Σ` and every `f ∈ L²(Ω)` the
weak problem `Lu = λu + f` (`B[u,v] = λ⟨u₀,v₀⟩ + ∫_Ω f v₀` for all `v`) has a
unique solution `u ∈ H₀¹(Ω)`, and for `λ ∈ Σ` uniqueness fails. -/
theorem existence_three (hK : IsCompactOperator (Op.opK Ω)) :
    ∃ S : Set ℝ, S.Countable ∧ (∀ C : ℝ, (S ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ S ↔ ∀ f : L2D Ω, ∃! u : H01 Ω, ∀ v : H01 Ω,
        Op.fullBilin Ω u v
          = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
            + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) := by
  obtain ⟨hc, hfin, hiff⟩ := (Op.gardingForm Ω).existence_three hK
  exact ⟨Op.sigmaSet Ω, hc, hfin, fun lam => (hiff lam).trans
    (forall_congr' fun f => existsUnique_congr fun u =>
      forall_congr' fun v => Op.gardingForm_iff Ω f u v)⟩

/-- **Boundedness of the resolvent.** For `λ ∉ Σ` there is a
constant `C > 0` such that every weak solution of `Lu = λu + f` with `f ∈ L²(Ω)`
satisfies `‖u‖_{L²} ≤ C ‖f‖_{L²}`. -/
theorem resolvent_bound (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
          + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, h⟩ := (Op.gardingForm Ω).resolvent_bound hK hlam
  exact ⟨C, hC, fun f u hu => h f u fun v => (Op.gardingForm_iff Ω f u v).mpr (hu v)⟩

end FullEllipticOp

end EllipticPdes.Sobolev
