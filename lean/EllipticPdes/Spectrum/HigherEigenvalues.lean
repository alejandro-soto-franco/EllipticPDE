/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.Variational

/-!
# Later eigenvalues by constrained minimisation

`EllipticPdes.Sobolev.exists_principal_eigenpair` names the first Dirichlet eigenvalue as the
infimum of the Rayleigh quotient over the unit `L²` sphere. Minimising over the part of that
sphere `L²`-orthogonal to a finite family of eigenfunctions names the next one, and repeating the
step names them all. This file supplies the step.

Two things have to be checked. The constraint is weakly closed, so
`EllipticPdes.Sobolev.exists_rayleigh_minimiser_on` applies to it and the minimum is attained;
and the minimiser is a weak eigenfunction of the whole space rather than only of the constrained
subspace. The second is where the multipliers drop out: a test vector splits as an admissible part
plus a combination of the `wᵢ`, and both `B[U, wᵢ]` and `⟪U, wᵢ⟫_{L²}` vanish, the first because
`wᵢ` is an eigenfunction and `U` is orthogonal to it, the second by the constraint itself.

## Main declarations

* `EllipticPdes.Variational.orthSubmodule`: the vectors `L²`-orthogonal to a finite family.
* `EllipticPdes.Variational.orthSubmodule_weaklyClosed`: the constraint passes to weak limits.
* `EllipticPdes.Variational.rayleigh_euler_lagrange_on`: the equation inside a submodule.
* `EllipticPdes.Variational.euler_lagrange_of_orthogonal_eigen`: the equation on the whole space.
* `EllipticPdes.Variational.exists_higher_eigenpair`: the constrained eigenpair, with its eigenvalue
  at least the principal one.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 1; Y. Guo, *Partial
Differential Equations*, Section IX.1.
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

/-! ### The orthogonality constraint -/

/-- The vectors of `V` whose images under `emb` are orthogonal to those of a finite family. -/
def orthSubmodule {n : ℕ} (w : Fin n → V) : Submodule ℝ V where
  carrier := {U | ∀ i, ⟪emb U, emb (w i)⟫ = 0}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro a b ha hb i
    rw [map_add, inner_add_left, ha i, hb i, add_zero]
  smul_mem' := by
    intro c a ha i
    rw [map_smul, real_inner_smul_left, ha i, mul_zero]

omit [CompleteSpace V] [CompleteSpace L] in
/-- `U ∈ orthSubmodule emb w` iff `emb U` is orthogonal to every `emb (w i)`. -/
@[simp] lemma mem_orthSubmodule {n : ℕ} {w : Fin n → V} {U : V} :
    U ∈ orthSubmodule emb w ↔ ∀ i, ⟪emb U, emb (w i)⟫ = 0 := Iff.rfl

/-- **Passage of the orthogonality constraint to weak limits.** Testing the weak convergence against
the adjoint image of each `wᵢ` turns it into convergence of the `L²` inner products. -/
lemma orthSubmodule_weaklyClosed {n : ℕ} (w : Fin n → V) (u : ℕ → V) (z : V)
    (hu : ∀ k, u k ∈ orthSubmodule emb w)
    (hz : ∀ v : V, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪z, v⟫)) :
    z ∈ orthSubmodule emb w := by
  intro i
  have hL2 : Tendsto (fun k => ⟪emb (u k), emb (w i)⟫) atTop
      (𝓝 ⟪emb z, emb (w i)⟫) := by
    simpa only [ContinuousLinearMap.adjoint_inner_right] using
      hz ((emb).adjoint (emb (w i)))
  have hconst : Tendsto (fun k => ⟪emb (u k), emb (w i)⟫) atTop (𝓝 0) := by
    simp only [fun k => hu k i]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hL2 hconst)

/-! ### The Rayleigh bound and the equation inside a submodule -/

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Rayleigh bound inside a submodule.** Rescaling stays in the submodule, so the bound of
`principalEigenvalue_mul_norm_sq_le` runs there unchanged. -/
theorem eigenvalueOn_mul_norm_sq_le (hco : IsCoercive B) (K : Submodule ℝ V) {U : V}
    (hUK : U ∈ K) :
    eigenvalueOn emb B (K : Set V) * ‖emb U‖ ^ 2 ≤ B U U := by
  rcases eq_or_ne (emb U) 0 with h0 | h0
  · rw [h0]
    simpa using bilin_self_nonneg hco U
  · have hpos : 0 < ‖emb U‖ := norm_pos_iff.mpr h0
    have hsphere : ‖emb (‖emb U‖⁻¹ • U)‖ = 1 := by
      simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      exact inv_mul_cancel₀ hpos.ne'
    have hmemK : (‖emb U‖⁻¹ • U) ∈ (K : Set V) := K.smul_mem _ hUK
    have hval : B (‖emb U‖⁻¹ • U) (‖emb U‖⁻¹ • U)
        = ‖emb U‖⁻¹ * (‖emb U‖⁻¹ * B U U) := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hle := eigenvalueOn_le emb hco hsphere hmemK
    rw [hval] at hle
    have hs2 : (0 : ℝ) < ‖emb U‖ ^ 2 := by positivity
    calc eigenvalueOn emb B (K : Set V) * ‖emb U‖ ^ 2
        ≤ ‖emb U‖⁻¹ * (‖emb U‖⁻¹ * B U U) * ‖emb U‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hs2.le
      _ = B U U := by field_simp

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Euler-Lagrange equation inside a submodule.** A minimiser over the unit `L²` sphere of
`K` satisfies the eigenvalue identity against every test vector of `K`. -/
theorem rayleigh_euler_lagrange_on (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (K : Submodule ℝ V) {U : V} (hU : ‖emb U‖ = 1) (hUK : U ∈ K)
    (hmin : B U U = eigenvalueOn emb B (K : Set V)) {W : V} (hVK : W ∈ K) :
    B U W = eigenvalueOn emb B (K : Set V) * ⟪emb U, emb W⟫ := by
  set lam := eigenvalueOn emb B (K : Set V) with hlamdef
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * (B U W - lam * ⟪emb U, emb W⟫)
        + t ^ 2 * (B W W - lam * ‖emb W‖ ^ 2) := by
    intro t
    have hmemK : U + t • W ∈ K := K.add_mem hUK (K.smul_mem _ hVK)
    have hmain := eigenvalueOn_mul_norm_sq_le emb hco K hmemK
    have hBexp : B (U + t • W) (U + t • W) = B U U + 2 * t * B U W + t ^ 2 * B W W := by
      have h1 : B (U + t • W) = B U + t • B W := by rw [map_add, map_smul]
      rw [h1]
      simp only [_root_.add_apply, _root_.smul_apply, map_add, map_smul,
        smul_eq_mul]
      rw [hsymm W U]
      ring
    have hNexp : ‖emb (U + t • W)‖ ^ 2
        = ‖emb U‖ ^ 2 + 2 * t * ⟪emb U, emb W⟫ + t ^ 2 * ‖emb W‖ ^ 2 := by
      have h1 : emb (U + t • W) = emb U + t • emb W := by
        rw [map_add, map_smul]
      rw [h1, ← real_inner_self_eq_norm_sq, real_inner_add_add_self, real_inner_smul_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
      ring
    rw [hBexp, hNexp, hmin, hU] at hmain
    nlinarith [hmain]
  have hb := eq_zero_of_quadratic_nonneg key
  linarith

/-! ### The equation on the whole space -/

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Constrained minimiser as a weak eigenfunction of the whole space.** Split a test vector
into its admissible part and a combination of the `wᵢ`; the second half contributes nothing to
either side. `B[U, wᵢ]` vanishes because `wᵢ` is an eigenfunction and `U` is orthogonal to it, and
`⟪U, wᵢ⟫_{L²}` vanishes by the constraint. -/
theorem euler_lagrange_of_orthogonal_eigen (hco : IsCoercive B)
    (hsymm : ∀ U W : V, B U W = B W U) {n : ℕ} {w : Fin n → V} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖emb (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪emb (w i), emb (w j)⟫ = 0)
    (hweig : ∀ i, ∀ W : V, B (w i) W = lam i * ⟪emb (w i), emb W⟫)
    {U : V} (hU : ‖emb U‖ = 1) (hUK : U ∈ orthSubmodule emb w)
    (hmin : B U U = eigenvalueOn emb B ((orthSubmodule emb w : Submodule ℝ V) : Set V))
    (W : V) :
    B U W
      = eigenvalueOn emb B ((orthSubmodule emb w : Submodule ℝ V) : Set V)
        * ⟪emb U, emb W⟫ := by
  set K : Submodule ℝ V := orthSubmodule emb w with hKdef
  set lamK := eigenvalueOn emb B (K : Set V) with hlamK
  obtain ⟨c, hcdef⟩ : ∃ c : Fin n → ℝ, c = fun i => ⟪emb W, emb (w i)⟫ := ⟨_, rfl⟩
  set W' : V := W - ∑ i, c i • w i with hV'def
  -- The `L²` class of the correction.
  have hsum : emb (∑ i, c i • w i) = ∑ i, c i • emb (w i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [map_smul])
  have hdiag : ∀ i, ⟪emb (w i), emb (w i)⟫ = 1 := by
    intro i
    rw [real_inner_self_eq_norm_sq, hwnorm i, one_pow]
  -- The admissible part.
  have hV'K : W' ∈ K := by
    intro j
    rw [hV'def, map_sub, inner_sub_left, hsum, sum_inner]
    have hpick : ∑ i, ⟪c i • emb (w i), emb (w j)⟫ = c j := by
      rw [Finset.sum_eq_single j]
      · rw [real_inner_smul_left, hdiag j, mul_one]
      · intro i _ hij
        rw [real_inner_smul_left, hworth i j hij, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hpick, hcdef]
    simp
  -- The correction pairs to zero on both sides.
  have hBzero : ∀ i, B U (w i) = 0 := by
    intro i
    rw [hsymm U (w i), hweig i U, real_inner_comm, hUK i, mul_zero]
  have hIzero : ∀ i, ⟪emb U, emb (w i)⟫ = 0 := hUK
  have hBsplit : B U W = B U W' := by
    have h1 : B U (∑ i, c i • w i) = 0 := by
      rw [map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [map_smul, smul_eq_mul, hBzero i, mul_zero]
    rw [hV'def, map_sub, h1, sub_zero]
  have hIsplit : ⟪emb U, emb W⟫ = ⟪emb U, emb W'⟫ := by
    have h1 : ⟪emb U, emb (∑ i, c i • w i)⟫ = 0 := by
      rw [hsum, inner_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [real_inner_smul_right, hIzero i, mul_zero]
    rw [hV'def, map_sub, inner_sub_right, h1, sub_zero]
  rw [hBsplit, hIsplit]
  exact rayleigh_euler_lagrange_on emb hco hsymm K hU hUK hmin hV'K

/-! ### The constrained eigenpair -/

/-- **Later eigenpair.** Minimising over the part of the unit `L²` sphere orthogonal to a
finite orthonormal family of eigenfunctions produces another eigenpair, whose eigenvalue is at
least the principal one. Iterating the step produces the whole sequence. -/
theorem exists_higher_eigenpair (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (hemb : IsCompactOperator (emb)) {n : ℕ} {w : Fin n → V} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖emb (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪emb (w i), emb (w j)⟫ = 0)
    (hweig : ∀ i, ∀ W : V, B (w i) W = lam i * ⟪emb (w i), emb W⟫)
    (hne : (rayleighSphere emb ∩ (orthSubmodule emb w : Set V)).Nonempty) :
    ∃ (U : V) (μ : ℝ), ‖emb U‖ = 1 ∧ U ∈ orthSubmodule emb w ∧ B U U = μ ∧
      principalEigenvalue emb B ≤ μ ∧
      ∀ W : V, B U W = μ * ⟪emb U, emb W⟫ := by
  obtain ⟨U, hU, hUK, hmin⟩ :=
    exists_rayleigh_minimiser_on emb hco hsymm hemb (orthSubmodule_weaklyClosed emb w) hne
  refine ⟨U, eigenvalueOn emb B ((orthSubmodule emb w : Submodule ℝ V) : Set V), hU, hUK,
    hmin, principalEigenvalue_le_eigenvalueOn emb hco hne, fun W => ?_⟩
  exact euler_lagrange_of_orthogonal_eigen emb hco hsymm hwnorm hworth hweig hU hUK hmin W

end EllipticPdes.Variational

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-! ### The Dirichlet instance -/

/-- The vectors of `H₀¹(Ω)` whose `L²` classes are orthogonal to those of a finite family. -/
def orthSubmodule {n : ℕ} (w : Fin n → H01 Ω) : Submodule ℝ (H01 Ω) :=
  Variational.orthSubmodule (embL2 Ω) w

/-- `U ∈ orthSubmodule w` iff `U` is `L²`-orthogonal to every `w i`. -/
@[simp] lemma mem_orthSubmodule {n : ℕ} {w : Fin n → H01 Ω} {U : H01 Ω} :
    U ∈ orthSubmodule w ↔ ∀ i, ⟪embL2 Ω U, embL2 Ω (w i)⟫ = 0 := Iff.rfl

/-- **Passage of the orthogonality constraint to weak limits.** -/
lemma orthSubmodule_weaklyClosed {n : ℕ} (w : Fin n → H01 Ω) (u : ℕ → H01 Ω) (z : H01 Ω)
    (hu : ∀ k, u k ∈ orthSubmodule w)
    (hz : ∀ v : H01 Ω, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪z, v⟫)) :
    z ∈ orthSubmodule w :=
  Variational.orthSubmodule_weaklyClosed (embL2 Ω) w u z hu hz

/-- **Rayleigh bound inside a submodule.** -/
theorem eigenvalueOn_mul_norm_sq_le (hco : IsCoercive B) (K : Submodule ℝ (H01 Ω)) {U : H01 Ω}
    (hUK : U ∈ K) :
    eigenvalueOn B (K : Set (H01 Ω)) * ‖embL2 Ω U‖ ^ 2 ≤ B U U :=
  Variational.eigenvalueOn_mul_norm_sq_le (embL2 Ω) hco K hUK

/-- **Euler-Lagrange equation inside a submodule.** A minimiser over the unit `L²` sphere of
`K` satisfies the eigenvalue identity against every test vector of `K`. -/
theorem rayleigh_euler_lagrange_on (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (K : Submodule ℝ (H01 Ω)) {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hUK : U ∈ K)
    (hmin : B U U = eigenvalueOn B (K : Set (H01 Ω))) {V : H01 Ω} (hVK : V ∈ K) :
    B U V = eigenvalueOn B (K : Set (H01 Ω)) * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  Variational.rayleigh_euler_lagrange_on (embL2 Ω) hco hsymm K hU hUK hmin hVK

/-- **Constrained minimiser as a weak eigenfunction of the whole space.** -/
theorem euler_lagrange_of_orthogonal_eigen (hco : IsCoercive B)
    (hsymm : ∀ U V : H01 Ω, B U V = B V U) {n : ℕ} {w : Fin n → H01 Ω} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫)
    {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hUK : U ∈ orthSubmodule w)
    (hmin : B U U = eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω)))
    (V : H01 Ω) :
    B U V
      = eigenvalueOn B ((orthSubmodule w : Submodule ℝ (H01 Ω)) : Set (H01 Ω))
        * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  Variational.euler_lagrange_of_orthogonal_eigen (embL2 Ω) hco hsymm hwnorm hworth hweig hU hUK
    hmin V

/-- **Later eigenpair.** Minimising over the part of the unit `L²` sphere orthogonal to a
finite orthonormal family of eigenfunctions produces another eigenpair, whose eigenvalue is at
least the principal one. Iterating the step produces the whole sequence. -/
theorem exists_higher_eigenpair (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) {n : ℕ} {w : Fin n → H01 Ω} {lam : Fin n → ℝ}
    (hwnorm : ∀ i, ‖embL2 Ω (w i)‖ = 1)
    (hworth : ∀ i j, i ≠ j → ⟪embL2 Ω (w i), embL2 Ω (w j)⟫ = 0)
    (hweig : ∀ i, ∀ V : H01 Ω, B (w i) V = lam i * ⟪embL2 Ω (w i), embL2 Ω V⟫)
    (hne : (rayleighSphere Ω ∩ (orthSubmodule w : Set (H01 Ω))).Nonempty) :
    ∃ (U : H01 Ω) (μ : ℝ), ‖embL2 Ω U‖ = 1 ∧ U ∈ orthSubmodule w ∧ B U U = μ ∧
      principalEigenvalue B ≤ μ ∧
      ∀ V : H01 Ω, B U V = μ * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  Variational.exists_higher_eigenpair (embL2 Ω) hco hsymm hRellich hwnorm hworth hweig hne

end EllipticPdes.Sobolev
