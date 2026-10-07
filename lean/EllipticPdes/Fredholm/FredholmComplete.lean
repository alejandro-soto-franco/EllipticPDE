/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.CompactOperator
public import EllipticPdes.Fredholm.Fredholm

/-!
# Complete Fredholm theory

Evans §6.2.3, Theorem 4.

`Fredholm.lean` realises the operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu` on `H₀¹(Ω)` as an
abstract `GardingForm` (`GardingForm.lean`), whose Riesz theory is developed over any Hilbert
space in `CompactOperator.lean`. This module states the consequences for the elliptic problem
as instances of the abstract theorems: the space

  `N = {u ∈ H₀¹(Ω) : B[u, v] = 0 for all v}`

of weak solutions of the homogeneous problem is the eigenspace of `opK` at `1`, the adjoint
problem is the transpose form `B(·, v)`, and the solvability criterion `Lu = f` solvable
`↔ f ⊥ N*` holds with `dim N = dim N*`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The space `N` of weak solutions of the homogeneous problem `Lu = 0`: the kernel of
the Riesz representative `opA` of the full divergence form. -/
def solSpace : Submodule ℝ (H01 Ω) := (Op.gardingForm Ω).solSpace

/-- Membership in `solSpace` is exactly being a weak solution of the homogeneous
problem: `B[u, v] = 0` against every `v ∈ H₀¹(Ω)`. -/
lemma mem_solSpace_iff (u : H01 Ω) :
    u ∈ Op.solSpace Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0 :=
  (Op.gardingForm Ω).mem_solSpace_iff u

/-- The homogeneous solution space is the eigenspace of the compact part `opK` at the
eigenvalue `1`: since `opA = opE ∘ (1 - opK)` with `opE` an equivalence,
`opA u = 0 ↔ opK u = u`. -/
lemma solSpace_eq_eigenspace :
    Op.solSpace Ω = Module.End.eigenspace (Op.opK Ω).toLinearMap 1 :=
  (Op.gardingForm Ω).solSpace_eq_eigenspace

/-- **Finite-dimensionality of the homogeneous solution space** (the finite-dimensionality
half of Evans §6.2.3, Theorem 4(ii)).
Under the Rellich-Kondrachov input (`opK` compact), the space of weak solutions of the
homogeneous problem `Lu = 0` is finite-dimensional: it is the eigenspace of the compact
operator `opK` at the nonzero eigenvalue `1`, and Riesz theory makes such eigenspaces
finite-dimensional. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    FiniteDimensional ℝ (Op.solSpace Ω) :=
  (Op.gardingForm Ω).finiteDimensional_solSpace hK

/-- **Closed range of the elliptic operator** (towards Evans §6.2.3, Theorem
4(ii)-(iii)). Under the Rellich-Kondrachov input the range of `opA` (the set of Riesz
representatives of solvable right-hand sides) is closed: `opA = opE ∘ (1 - opK)` with `opE` a
homeomorphism, and `1 - opK` has closed range by Riesz theory. This is the geometric
input for the solvability criterion `Lu = f solvable ↔ f ⊥ N*`. -/
theorem isClosed_range_opA (hK : IsCompactOperator (Op.opK Ω)) :
    IsClosed (Set.range (Op.opA Ω)) :=
  (Op.gardingForm Ω).isClosed_range_opA hK

/-- The **adjoint solution space** `N*`: the kernel of the Hilbert adjoint of `opA`,
which is exactly the space of weak solutions of the **transpose problem**
`B[v, u] = 0` for all `v` (the adjoint bilinear form and adjoint problem defined ahead
of Evans §6.2.3, Theorem 4: the adjoint problem is the transpose form, with no
differentiability demanded of the coefficients). -/
def solSpaceStar : Submodule ℝ (H01 Ω) := (Op.gardingForm Ω).solSpaceStar

/-- Membership in `solSpaceStar` is exactly being a weak solution of the transpose
problem: `B[v, u] = 0` against every `v ∈ H₀¹(Ω)`, the transpose counterpart of
`mem_solSpace_iff`. -/
lemma mem_solSpaceStar_iff (u : H01 Ω) :
    u ∈ Op.solSpaceStar Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω v u = 0 :=
  (Op.gardingForm Ω).mem_solSpaceStar_iff u

/-- **Solvability criterion** (Evans §6.2.3, Theorem 4(iii)). Under the
Rellich-Kondrachov input, the weak problem `Lu = f` is solvable exactly when `f`
annihilates the adjoint solution space: `∃u ∀v, B[u, v] = f(v)` iff `f(w) = 0` for
every weak solution `w` of the transpose problem `B[v, w] = 0`. The proof is closed
range (`isClosed_range_opA`) plus the Hilbert-space duality
`range A = (ker A†)ᗮ`. -/
theorem solvable_iff_orthogonal_solSpaceStar (hK : IsCompactOperator (Op.opK Ω))
    (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ ∀ w ∈ Op.solSpaceStar Ω, f w = 0 :=
  (Op.gardingForm Ω).solvable_iff_orthogonal_solSpaceStar hK f

/-- **`dim N = dim N*` for the elliptic problem** (Evans §6.2.3, Theorem 4(ii)). The space of
weak solutions of the homogeneous problem and the space of weak solutions of the transpose
problem have the same (finite) dimension. The factorisation `opA = opE ∘ (1 - opK)` maps
`solSpaceStar = ker(opA†)` onto `ker(1 - opK†)` along the bijection `(opE)†`, and the abstract
index theorem `finrank_ker_one_sub_adjoint_eq` applies. -/
theorem finrank_solSpaceStar_eq_finrank_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    Module.finrank ℝ (Op.solSpaceStar Ω) = Module.finrank ℝ (Op.solSpace Ω) :=
  (Op.gardingForm Ω).finrank_solSpaceStar_eq_finrank_solSpace hK

/-- **Fredholm alternative for the elliptic Dirichlet problem** (Evans §6.2.3, Theorem 4).
Assume the operator `opK` is compact: the Rellich-Kondrachov input, that `H₀¹(Ω) ↪ L²(Ω)` is a
compact embedding. Then exactly one of two alternatives holds: either the homogeneous problem
`Lu = 0` has a nontrivial weak solution `u ≠ 0` (`∀ v, B[u, v] = 0`), or the inhomogeneous
problem `Lu = f` has a unique weak solution for every continuous functional `f`. -/
theorem fredholm_alternative (hK : IsCompactOperator (Op.opK Ω)) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) :=
  (Op.gardingForm Ω).fredholm_alternative hK

/-- **Fredholm corollary** (the usual working form, Evans §6.2.3): if the homogeneous problem
`Lu = 0` has only the trivial weak solution, then `Lu = f` has a unique weak solution for every
`f`. Uniqueness of the homogeneous problem rules out the eigenvalue alternative. -/
theorem fredholm_unique_imp_exists (hK : IsCompactOperator (Op.opK Ω))
    (huniq : ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = 0) → u = 0)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v :=
  (Op.gardingForm Ω).fredholm_unique_imp_exists hK huniq f

end FullEllipticOp

end EllipticPdes.Sobolev
