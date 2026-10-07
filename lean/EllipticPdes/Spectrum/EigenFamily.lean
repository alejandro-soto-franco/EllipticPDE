/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.HigherEigenvalues

/-!
# Eigenvalue sequence by iterated constrained minimisation

`EllipticPdes.Sobolev.exists_higher_eigenpair` produces one eigenpair orthogonal to a given
finite family. Iterating it produces, for every `n`, an `L²`-orthonormal family of `n` weak
eigenfunctions whose eigenvalues increase. That is the variational construction of the Dirichlet
spectrum, and it names every eigenvalue by a Rayleigh quotient rather than one at a time through
the spectral theorem, which is what `EllipticPdes.Sobolev.solOp_spectral` does.

The induction records one thing beyond the conclusion: every eigenvalue produced so far is at
most the infimum over the current constraint submodule. That is what makes the next eigenvalue
the largest, since the next one is exactly that infimum, and the constraint submodule shrinks at
each step, so the infima increase.

The recursion needs a vector orthogonal to the family at every stage, which is infinite
dimensionality of the `L²` image of `H₀¹(Ω)`. It is a hypothesis here, stated as the existence
of a single vector at each stage rather than as a dimension count.

## Main declarations

* `EllipticPdes.Variational.eigenvalueOn_mono`: tightening the constraint raises the infimum.
* `EllipticPdes.Variational.orthSubmodule_snoc_subset`: appending shrinks the constraint.
* `EllipticPdes.Variational.exists_eigen_family`: the orthonormal family and its increasing
  eigenvalues.
* `EllipticPdes.Variational.principalEigenvalue_le_of_eigen_family`: every eigenvalue of such a
  family is at least the principal one.
* `EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded`: the instance at `-Δ` on a bounded
  measurable domain, reading `0 < λ₁ ≤ ⋯ ≤ λₙ`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1; Y. Guo, *Partial
Differential Equations*, Section VII.5.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Variational

open EllipticPdes.Analysis

variable {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L] (emb : V →L[ℝ] L)
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-! ### Monotonicity of the constrained infimum -/

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Tightening the constraint raises the infimum.** -/
lemma eigenvalueOn_mono (hco : IsCoercive B) {S S' : Set V} (hsub : S ⊆ S')
    (hne : (rayleighSphere emb ∩ S).Nonempty) :
    eigenvalueOn emb B S' ≤ eigenvalueOn emb B S :=
  csInf_le_csInf (rayleighValuesOn_bddBelow emb hco S') (hne.image _)
    (Set.image_mono (Set.inter_subset_inter_right _ hsub))

omit [CompleteSpace V] [CompleteSpace L] in
/-- A submodule with a vector of nonzero `L²` class meets the unit `L²` sphere: rescale. -/
lemma rayleighSphere_inter_nonempty {K : Submodule ℝ V}
    (h : ∃ U ∈ K, emb U ≠ 0) : (rayleighSphere emb ∩ (K : Set V)).Nonempty := by
  obtain ⟨U, hUK, hU⟩ := h
  have hpos : 0 < ‖emb U‖ := norm_pos_iff.mpr hU
  refine ⟨‖emb U‖⁻¹ • U, ?_, K.smul_mem _ hUK⟩
  simp only [rayleighSphere, Set.mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hpos.ne'

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Appending a vector shrinks the constraint submodule.** -/
lemma orthSubmodule_snoc_subset {n : ℕ} (w : Fin n → V) (U : V) :
    ((orthSubmodule emb (Fin.snoc w U : Fin (n + 1) → V)) : Set V)
      ⊆ ((orthSubmodule emb w : Submodule ℝ V) : Set V) := by
  intro W hV i
  have h := hV i.castSucc
  rwa [Fin.snoc_castSucc] at h

/-! ### The family -/

/-- **Eigenvalue sequence.** For every `n` there is an `L²`-orthonormal family of `n` weak
eigenfunctions of `B` whose eigenvalues increase with the index. The hypothesis `hdim` supplies,
at each stage, a vector of nonzero `L²` class orthogonal to the family built so far; on a bounded
domain it is the infinite dimensionality of `H₀¹(Ω)`.

The fifth conclusion is the induction's own invariant: every eigenvalue produced so far is at
most the infimum over the current constraint submodule, which is what the next step returns. -/
theorem exists_eigen_family (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (hemb : IsCompactOperator (emb))
    (hdim : ∀ (m : ℕ) (v : Fin m → V), ∃ U ∈ orthSubmodule emb v, emb U ≠ 0) (n : ℕ) :
    ∃ (w : Fin n → V) (lam : Fin n → ℝ),
      (∀ i, ‖emb (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪emb (w i), emb (w j)⟫ = 0) ∧
      (∀ i, ∀ W : V, B (w i) W = lam i * ⟪emb (w i), emb W⟫) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, lam i ≤ eigenvalueOn emb B ((orthSubmodule emb w : Submodule ℝ V) : Set V)) := by
  induction n with
  | zero =>
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨w, lam, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨U, hUnorm, hUmem, hUmin⟩ :=
      exists_rayleigh_minimiser_on emb hco hsymm hemb (orthSubmodule_weaklyClosed emb w)
        (rayleighSphere_inter_nonempty emb (hdim n w))
    set μ : ℝ := eigenvalueOn emb B ((orthSubmodule emb w : Submodule ℝ V) : Set V) with hμ
    have hUeq : ∀ W : V, B U W = μ * ⟪emb U, emb W⟫ := fun W =>
      euler_lagrange_of_orthogonal_eigen emb hco hsymm h1 h2 h3 hUnorm hUmem hUmin W
    have hmuv : μ ≤ eigenvalueOn emb B
        ((orthSubmodule emb (Fin.snoc w U : Fin (n + 1) → V) : Submodule ℝ V) :
          Set V) :=
      eigenvalueOn_mono emb hco (orthSubmodule_snoc_subset emb w U)
        (rayleighSphere_inter_nonempty emb (hdim (n + 1) (Fin.snoc w U)))
    refine ⟨Fin.snoc w U, Fin.snoc lam μ, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]
    · exact ⟨h1, hUnorm⟩
    · exact ⟨fun i => ⟨fun j hij => h2 i j fun h => hij (congrArg Fin.castSucc h),
        fun _ => (real_inner_comm _ _).trans (hUmem i)⟩, fun i _ => hUmem i,
        fun h => absurd rfl h⟩
    · exact ⟨h3, hUeq⟩
    · exact ⟨fun i => ⟨fun j hij => h4 i j (Fin.castSucc_le_castSucc_iff.mp hij), fun _ => h5 i⟩,
        fun i hi => absurd (Fin.castSucc_lt_last i) (not_lt.mpr hi), fun _ => le_rfl⟩
    · exact ⟨fun i => (h5 i).trans hmuv, hmuv⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Every eigenvalue of an orthonormal family is at least the principal one.** A member of the
family has unit `L²` norm and so is nonzero, which is what
`principalEigenvalue_le_of_weak_eigenvector` asks for. -/
theorem principalEigenvalue_le_of_eigen_family (hco : IsCoercive B) {n : ℕ} {w : Fin n → V}
    {lam : Fin n → ℝ} (hwnorm : ∀ i, ‖emb (w i)‖ = 1)
    (hweig : ∀ i, ∀ W : V, B (w i) W = lam i * ⟪emb (w i), emb W⟫) (i : Fin n) :
    principalEigenvalue emb B ≤ lam i := by
  refine principalEigenvalue_le_of_weak_eigenvector emb hco (fun h0 => ?_) (hweig i)
  have h := hwnorm i
  rw [h0] at h
  simp at h

end EllipticPdes.Variational

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-! ### The Dirichlet instance -/

/-- **Tightening the constraint raises the infimum.** -/
lemma eigenvalueOn_mono (hco : IsCoercive B) {S S' : Set (H01 Ω)} (hsub : S ⊆ S')
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    eigenvalueOn B S' ≤ eigenvalueOn B S :=
  Variational.eigenvalueOn_mono (embL2 Ω) hco hsub hne

/-- A submodule with a vector of nonzero `L²` class meets the unit `L²` sphere: rescale. -/
lemma rayleighSphere_inter_nonempty {K : Submodule ℝ (H01 Ω)}
    (h : ∃ U ∈ K, embL2 Ω U ≠ 0) : (rayleighSphere Ω ∩ (K : Set (H01 Ω))).Nonempty :=
  Variational.rayleighSphere_inter_nonempty (embL2 Ω) h

/-- **Appending a vector shrinks the constraint submodule.** -/
lemma orthSubmodule_snoc_subset {n : ℕ} (w : Fin n → H01 Ω) (U : H01 Ω) :
    ((orthSubmodule (Fin.snoc w U : Fin (n + 1) → H01 Ω)) : Set (H01 Ω))
      ⊆ ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)) :=
  Variational.orthSubmodule_snoc_subset (embL2 Ω) w U

/-- **Eigenvalue sequence.** For every `n` there is an `L²`-orthonormal family of `n` weak
eigenfunctions of `B` whose eigenvalues increase with the index. The hypothesis `hdim` supplies,
at each stage, a vector of nonzero `L²` class orthogonal to the family built so far; on a bounded
domain it is the infinite dimensionality of `H₀¹(Ω)`.

The fifth conclusion is the induction's own invariant: every eigenvalue produced so far is at
most the infimum over the current constraint submodule, which is what the next step returns. -/
theorem exists_eigen_family (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω))
    (hdim : ∀ (m : ℕ) (v : Fin m → H01 Ω), ∃ U ∈ orthSubmodule v, embL2 Ω U ≠ 0) (n : ℕ) :
    ∃ (w : Fin n → H01 Ω) (lam : Fin n → ℝ),
      (∀ i, ‖embL2 Ω (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0) ∧
      (∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, lam i ≤ eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω))) :=
  Variational.exists_eigen_family (embL2 Ω) hco hsymm hRellich hdim n

/-- **Every eigenvalue of an orthonormal family is at least the principal one.** -/
theorem principalEigenvalue_le_of_eigen_family (hco : IsCoercive B) {n : ℕ} {w : Fin n → H01 Ω}
    {lam : Fin n → ℝ} (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) (i : Fin n) :
    principalEigenvalue B ≤ lam i :=
  Variational.principalEigenvalue_le_of_eigen_family (embL2 Ω) hco hwnorm hweig i

/-- **Dirichlet eigenvalue sequence on a bounded domain.** For every `n` there is an
`L²`-orthonormal family of `n` weak solutions of `-Δw = λw` with `0 < λ₁ ≤ ⋯ ≤ λₙ`. Boundedness
and measurability of `Ω` discharge coercivity and the compact embedding; `hdim` is the infinite
dimensionality of `H₀¹(Ω)`, stated as a vector at each stage. -/
theorem dirichlet_eigen_family_of_bounded {m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hdim : ∀ (k : ℕ) (v : Fin k → H01 Ω), ∃ U ∈ orthSubmodule v, embL2 Ω U ≠ 0) (n : ℕ) :
    ∃ (w : Fin n → H01 Ω) (lam : Fin n → ℝ),
      (∀ i, ‖embL2 Ω (w i)‖ = 1) ∧
      (∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0) ∧
      (∀ i, 0 < lam i) ∧
      (∀ i j, i ≤ j → lam i ≤ lam j) ∧
      (∀ i, ∀ V : H01 Ω, laplaceBilin Ω (w i) V
        = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫) := by
  have hco := EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb
  obtain ⟨U0, -, hU0⟩ := hdim 0 Fin.elim0
  have hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0 := ⟨U0, hU0⟩
  obtain ⟨w, lam, h1, h2, h3, h4, -⟩ :=
    exists_eigen_family hco (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hdim n
  exact ⟨w, lam, h1, h2, fun i => lt_of_lt_of_le (principalEigenvalue_pos hco hne)
    (principalEigenvalue_le_of_eigen_family hco h1 h3 i), h4, h3⟩

end EllipticPdes.Sobolev
