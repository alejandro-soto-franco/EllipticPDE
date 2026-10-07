/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Spectrum.RellichDischarge
public import EllipticPdes.Analysis.WeakCompactness
public import EllipticPdes.Analysis.DirectMethodForm
public import EllipticPdes.Poincare.BoundedDomain

/-!
# Variational characterisation of the principal eigenvalue

`EllipticPdes.Sobolev.solOp_spectral` produces the Dirichlet eigenvalues from the spectral theorem
for the compact self-adjoint solution operator, one eigenvalue at a time and with no formula for
any of them. This file gives the first eigenvalue a formula: it is the infimum of the Rayleigh
quotient

`λ₁ = inf { B[U, U] : U ∈ H₀¹(Ω), ‖U‖_{L²(Ω)} = 1 }`,

the infimum is attained, and a minimiser is a weak eigenfunction at that eigenvalue. Every weak
eigenvalue of `B` is at least `λ₁`, so the name is the theorem.

Everything up to the Dirichlet instance is stated for a bounded linear map `emb : V →L[ℝ] L`
between real Hilbert spaces and a coercive form `B` on `V` (namespace
`EllipticPdes.Variational`); the Euclidean names are the instance `emb = embL2 Ω`.

The proof is the direct method in the abstract setting. Coercivity bounds a minimising sequence in
`H₀¹(Ω)`, `EllipticPdes.Analysis.exists_weakLimit` extracts a weak limit, and the Rellich compact
embedding `embL2 Ω` takes the constraint to that limit along a further subsequence. Weak lower
semicontinuity of the form is the expansion of `0 ≤ B[Uₖ - w, Uₖ - w]` together with
`B[Uₖ, w] → B[w, w]`, which needs symmetry and nothing else. The Euler-Lagrange step is a
one-variable argument: `t ↦ B[U + tV, U + tV] - λ₁‖U + tV‖²_{L²}` is a quadratic that vanishes at
`t = 0` and is nonnegative everywhere, so its linear coefficient vanishes.

`EllipticPdes.Embedding.exists_minimiser_of_lt` runs the same method at a subcritical `L^q`
constraint, where the compactness comes from `rellichEmbL_isCompact_of_lt`. The two files differ in
which compact embedding does the work and in whether the constraint is quadratic; at `q = 2` the
constraint is quadratic and the minimiser satisfies a linear equation, which is this file.

## Main declarations

* `EllipticPdes.Sobolev.principalEigenvalue`: the infimum of the Rayleigh quotient.
* `EllipticPdes.Sobolev.principalEigenvalue_mul_norm_sq_le`: `λ₁‖U‖²_{L²} ≤ B[U, U]` for every
  `U`, the Rayleigh quotient bound off the constraint set.
* `EllipticPdes.Sobolev.exists_rayleigh_minimiser`: the infimum is attained.
* `EllipticPdes.Sobolev.rayleigh_euler_lagrange`: a minimiser is a weak eigenfunction.
* `EllipticPdes.Sobolev.exists_principal_eigenpair`: the two previous statements combined.
* `EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen`: no weak eigenvalue is smaller.
* `EllipticPdes.Sobolev.dirichlet_principal_eigenpair`: the instance at `-Δ` on a bounded
  measurable domain, with the compact embedding discharged by `embL2_isCompact`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §6.5.1, Theorem 2; Y. Guo, *Partial
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

/-! ### The Rayleigh quotient and its infimum -/

/-- The unit sphere of `L` pulled back along `emb`, the constraint set of the Rayleigh problem. -/
def rayleighSphere : Set V :=
  {U | ‖emb U‖ = 1}

/-- The values a bilinear form takes on the `emb`-unit sphere. -/
def rayleighValues (B : V →L[ℝ] V →L[ℝ] ℝ) : Set ℝ :=
  (fun U => B U U) '' rayleighSphere emb

/-- **Principal eigenvalue** of a symmetric coercive form on `V`: the infimum of the Rayleigh
quotient `B[U, U]` over the vectors with `‖emb U‖ = 1`. -/
def principalEigenvalue (B : V →L[ℝ] V →L[ℝ] ℝ) : ℝ := sInf (rayleighValues emb B)

omit [CompleteSpace V] [CompleteSpace L] in
/-- The constraint set is inhabited as soon as some element has a nonzero image under `emb`:
rescale. -/
lemma rayleighSphere_nonempty (hne : ∃ W : V, emb W ≠ 0) :
    (rayleighSphere emb).Nonempty := by
  obtain ⟨W, hV⟩ := hne
  have hpos : 0 < ‖emb W‖ := norm_pos_iff.mpr hV
  refine ⟨‖emb W‖⁻¹ • W, ?_⟩
  simp only [rayleighSphere, Set.mem_ofPred_eq, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos)]
  exact inv_mul_cancel₀ hpos.ne'

omit [CompleteSpace V] [CompleteSpace L] in
/-- Positive semidefiniteness bounds the Rayleigh values below by zero. -/
lemma rayleighValues_bddBelow (hco : IsCoercive B) : BddBelow (rayleighValues emb B) :=
  ⟨0, by rintro _ ⟨U, -, rfl⟩; exact bilin_self_nonneg hco U⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- The infimum is a lower bound on the constraint set. -/
lemma principalEigenvalue_le (hco : IsCoercive B) {U : V} (hU : ‖emb U‖ = 1) :
    principalEigenvalue emb B ≤ B U U :=
  csInf_le (rayleighValues_bddBelow emb hco) ⟨U, hU, rfl⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Rayleigh bound off the constraint set**: `λ₁‖U‖²_{L²} ≤ B[U, U]` for every `U`. On the
constraint set this is the definition of the infimum, and elsewhere it follows by rescaling. -/
theorem principalEigenvalue_mul_norm_sq_le (hco : IsCoercive B) (U : V) :
    principalEigenvalue emb B * ‖emb U‖ ^ 2 ≤ B U U := by
  rcases eq_or_ne (emb U) 0 with h0 | h0
  · rw [h0]
    simpa using bilin_self_nonneg hco U
  · have hpos : 0 < ‖emb U‖ := norm_pos_iff.mpr h0
    have hsphere : ‖emb (‖emb U‖⁻¹ • U)‖ = 1 := by
      simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      exact inv_mul_cancel₀ hpos.ne'
    have hval : B (‖emb U‖⁻¹ • U) (‖emb U‖⁻¹ • U)
        = ‖emb U‖⁻¹ * (‖emb U‖⁻¹ * B U U) := by
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hle := principalEigenvalue_le emb hco hsphere
    rw [hval] at hle
    have hs2 : (0 : ℝ) < ‖emb U‖ ^ 2 := by positivity
    calc principalEigenvalue emb B * ‖emb U‖ ^ 2
        ≤ ‖emb U‖⁻¹ * (‖emb U‖⁻¹ * B U U) * ‖emb U‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle hs2.le
      _ = B U U := by field_simp

omit [CompleteSpace V] [CompleteSpace L] in
/-- Coercivity bounds the principal eigenvalue below: on the constraint set `1 = ‖emb U‖
≤ ‖emb‖ ‖U‖`, so `C / ‖emb‖² ≤ C ‖U‖² ≤ B[U, U]`. -/
lemma le_principalEigenvalue_of_coercive (hne : ∃ W : V, emb W ≠ 0) {C : ℝ} (hC : 0 < C)
    (hcoer : ∀ U : V, C * ‖U‖ * ‖U‖ ≤ B U U) : C / ‖emb‖ ^ 2 ≤ principalEigenvalue emb B := by
  obtain ⟨W, hW⟩ := hne
  have hE : 0 < ‖emb‖ := norm_pos_iff.mpr fun h => hW (by simp [h])
  refine le_csInf ((rayleighSphere_nonempty emb ⟨W, hW⟩).image _) ?_
  rintro _ ⟨U, hU, rfl⟩
  change C / ‖emb‖ ^ 2 ≤ B U U
  have h1 : (1 : ℝ) ≤ ‖emb‖ * ‖U‖ := hU ▸ emb.le_opNorm U
  have h2 : 1 ≤ (‖emb‖ * ‖U‖) * (‖emb‖ * ‖U‖) := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hcoer U, mul_le_mul_of_nonneg_left h2 hC.le]

omit [CompleteSpace V] [CompleteSpace L] in
/-- The principal eigenvalue of a coercive form is positive. -/
theorem principalEigenvalue_pos (hco : IsCoercive B) (hne : ∃ W : V, emb W ≠ 0) :
    0 < principalEigenvalue emb B := by
  obtain ⟨C, hC, hcoer⟩ := id hco
  obtain ⟨W, hW⟩ := hne
  have hE : 0 < ‖emb‖ := norm_pos_iff.mpr fun h => hW (by simp [h])
  exact lt_of_lt_of_le (by positivity)
    (le_principalEigenvalue_of_coercive emb ⟨W, hW⟩ hC hcoer)

/-! ### The Euler-Lagrange equation -/

/-- A quadratic in `t` that vanishes at `t = 0` and is nonnegative everywhere has no linear
term. -/
lemma eq_zero_of_quadratic_nonneg {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a) :
    b = 0 := by
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have hεpos : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  have hεa : 1 / (|a| + 1) * a < 2 := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : (0 : ℝ) < |a| + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2]
    linarith
  have hneg := h (-(1 / (|a| + 1) * b))
  nlinarith [mul_pos (mul_pos hεpos hb2) (show (0 : ℝ) < 2 - 1 / (|a| + 1) * a by linarith)]

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Euler-Lagrange equation of the Rayleigh problem.** A minimiser on the `emb`-unit sphere is
a weak eigenfunction at the principal eigenvalue: `B[U, W] = λ₁⟪U, W⟫_{L²}` for every `W`. -/
theorem rayleigh_euler_lagrange (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    {U : V} (hU : ‖emb U‖ = 1) (hmin : B U U = principalEigenvalue emb B) (W : V) :
    B U W = principalEigenvalue emb B * ⟪emb U, emb W⟫ := by
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * (B U W - principalEigenvalue emb B * ⟪emb U, emb W⟫)
        + t ^ 2 * (B W W - principalEigenvalue emb B * ‖emb W‖ ^ 2) := by
    intro t
    have hmain := principalEigenvalue_mul_norm_sq_le emb hco (U + t • W)
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

/-! ### The Rayleigh problem under a further constraint -/

/-- The values a form takes on the `emb`-unit sphere inside a set `S`. -/
def rayleighValuesOn (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Set V) : Set ℝ :=
  (fun U => B U U) '' (rayleighSphere emb ∩ S)

/-- The infimum of the Rayleigh quotient over the `emb`-unit sphere inside `S`. Taking `S` to be
the vectors `L²`-orthogonal to the earlier eigenfunctions gives the later eigenvalues. -/
def eigenvalueOn (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Set V) : ℝ :=
  sInf (rayleighValuesOn emb B S)

omit [CompleteSpace V] [CompleteSpace L] in
/-- With no constraint the values are those of the whole sphere. -/
lemma rayleighValuesOn_univ : rayleighValuesOn emb B Set.univ = rayleighValues emb B := by
  rw [rayleighValuesOn, rayleighValues, Set.inter_univ]

omit [CompleteSpace V] [CompleteSpace L] in
/-- With no constraint the infimum is the principal eigenvalue. -/
lemma eigenvalueOn_univ : eigenvalueOn emb B Set.univ = principalEigenvalue emb B := by
  rw [eigenvalueOn, rayleighValuesOn_univ, principalEigenvalue]

omit [CompleteSpace V] [CompleteSpace L] in
/-- Positive semidefiniteness bounds the constrained values below by zero. -/
lemma rayleighValuesOn_bddBelow (hco : IsCoercive B) (S : Set V) :
    BddBelow (rayleighValuesOn emb B S) :=
  ⟨0, by rintro _ ⟨U, -, rfl⟩; exact bilin_self_nonneg hco U⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- The constrained infimum is a lower bound on the constrained sphere. -/
lemma eigenvalueOn_le (hco : IsCoercive B) {S : Set V} {U : V}
    (hU : ‖emb U‖ = 1) (hUS : U ∈ S) : eigenvalueOn emb B S ≤ B U U :=
  csInf_le (rayleighValuesOn_bddBelow emb hco S) ⟨U, ⟨hU, hUS⟩, rfl⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Tightening the constraint raises the infimum.** -/
lemma principalEigenvalue_le_eigenvalueOn (hco : IsCoercive B) {S : Set V}
    (hne : (rayleighSphere emb ∩ S).Nonempty) :
    principalEigenvalue emb B ≤ eigenvalueOn emb B S := by
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨U, hU, rfl⟩
  exact principalEigenvalue_le emb hco hU.1

/-! ### Existence of a minimiser -/

/-- **Attainment of the infimum of the Rayleigh quotient over a weakly closed set.** Coercivity
bounds a minimising sequence, weak compactness supplies a limit, the constraint `S` passes to that
limit by hypothesis, and the compact map `emb` takes the unit `emb`-norm to it. -/
theorem exists_rayleigh_minimiser_on (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (hRellich : IsCompactOperator (emb)) {S : Set V}
    (hSclosed : ∀ (u : ℕ → V) (w : V), (∀ k, u k ∈ S) →
      (∀ v : V, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) → w ∈ S)
    (hne : (rayleighSphere emb ∩ S).Nonempty) :
    ∃ U : V, ‖emb U‖ = 1 ∧ U ∈ S ∧ B U U = eigenvalueOn emb B S := by
  obtain ⟨C, hC, hcoer⟩ := id hco
  have hbdd : BddBelow (rayleighValuesOn emb B S) := rayleighValuesOn_bddBelow emb hco S
  -- A minimising sequence.
  obtain ⟨r, hrmono, hrlim, hrmem⟩ := exists_seq_tendsto_sInf (hne.image _) hbdd
  choose U hUmem hUval using hrmem
  have hUs : ∀ n, ‖emb (U n)‖ = 1 := fun n => (hUmem n).1
  have hUS : ∀ n, U n ∈ S := fun n => (hUmem n).2
  set M : ℝ := Real.sqrt (r 0 / C) with hMdef
  have hMbound : ∀ n, ‖U n‖ ≤ M := by
    intro n
    have h2 : ‖U n‖ ^ 2 ≤ r 0 / C := by
      rw [le_div_iff₀ hC]
      nlinarith [hcoer (U n), hrmono (Nat.zero_le n), hUval n]
    calc ‖U n‖ = Real.sqrt (‖U n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ M := Real.sqrt_le_sqrt h2
  -- Weak compactness.
  obtain ⟨w, φ, hφ, hweak⟩ := exists_weakLimit (u := U) hMbound
  have hweakL2 : ∀ g : L,
      Tendsto (fun k => ⟪emb (U (φ k)), g⟫) atTop (𝓝 ⟪emb w, g⟫) := by
    intro g
    simpa only [ContinuousLinearMap.adjoint_inner_right] using hweak ((emb).adjoint g)
  -- Rellich gives a further subsequence converging strongly in `L²`.
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hcptL : IsCompactOperator ((emb).toLinearMap) := hRellich
  have hcl :=
    (isCompactOperator_iff_isCompact_closure_image_closedBall (emb).toLinearMap hM1).mp hcptL
  have hmemcl : ∀ k, emb (U (φ k))
      ∈ closure (⇑(emb).toLinearMap '' Metric.closedBall (0 : V) (M + 1)) :=
    fun k => subset_closure ⟨U (φ k), by
      simpa [Metric.mem_closedBall, dist_zero_right] using (hMbound (φ k)).trans (by linarith), rfl⟩
  obtain ⟨z, -, ψ, hψ, hψtend⟩ := hcl.tendsto_subseq hmemcl
  -- The strong limit is the image under `emb` of the weak limit.
  have hzw : z = emb w := by
    refine ext_inner_right ℝ (fun g => ?_)
    have hstrong : Tendsto (fun j => ⟪emb (U (φ (ψ j))), g⟫) atTop (𝓝 ⟪z, g⟫) := by
      simpa [Function.comp_def] using hψtend.inner (tendsto_const_nhds (x := g))
    exact tendsto_nhds_unique hstrong ((hweakL2 g).comp hψ.tendsto_atTop)
  have hwnorm : ‖emb w‖ = 1 := by
    have h1 : Tendsto (fun j => ‖emb (U (φ (ψ j)))‖) atTop (𝓝 ‖z‖) := by
      simpa [Function.comp_def] using (continuous_norm.tendsto z).comp hψtend
    have h2 : Tendsto (fun j => ‖emb (U (φ (ψ j)))‖) atTop (𝓝 1) := by
      simp only [hUs]
      exact tendsto_const_nhds
    rw [← hzw]
    exact tendsto_nhds_unique h1 h2
  have hwS : w ∈ S := hSclosed (fun k => U (φ k)) w (fun k => hUS (φ k)) hweak
  -- Weak lower semicontinuity of the form.
  have hBUU : Tendsto (fun n => B (U n) (U n)) atTop (𝓝 (eigenvalueOn emb B S)) := by
    simpa only [hUval, eigenvalueOn, rayleighValuesOn] using hrlim
  have hlsc : B w w ≤ eigenvalueOn emb B S := by
    refine bilin_le_of_weakLimit hco hsymm hweak ?_
    simpa [Function.comp_def] using hBUU.comp hφ.tendsto_atTop
  exact ⟨w, hwnorm, hwS, le_antisymm hlsc (eigenvalueOn_le emb hco hwnorm hwS)⟩

/-- **Attainment of the infimum of the Rayleigh quotient.** The unconstrained case. -/
theorem exists_rayleigh_minimiser (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (hRellich : IsCompactOperator (emb)) (hne : ∃ W : V, emb W ≠ 0) :
    ∃ U : V, ‖emb U‖ = 1 ∧ B U U = principalEigenvalue emb B := by
  have hne' : (rayleighSphere emb ∩ Set.univ).Nonempty := by
    simpa using rayleighSphere_nonempty emb hne
  obtain ⟨U, hU, -, hmin⟩ :=
    exists_rayleigh_minimiser_on emb hco hsymm hRellich (S := Set.univ)
      (fun _ _ _ _ => Set.mem_univ _) hne'
  exact ⟨U, hU, by rwa [eigenvalueOn_univ] at hmin⟩

/-- **Principal eigenpair.** For a symmetric coercive form with the compact map `emb`
there is a `U` of unit `emb`-norm attaining the infimum of the Rayleigh quotient, and it solves the
weak eigenvalue problem at that value. -/
theorem exists_principal_eigenpair (hco : IsCoercive B) (hsymm : ∀ U W : V, B U W = B W U)
    (hRellich : IsCompactOperator (emb)) (hne : ∃ W : V, emb W ≠ 0) :
    ∃ U : V, ‖emb U‖ = 1 ∧ B U U = principalEigenvalue emb B ∧
      ∀ W : V, B U W = principalEigenvalue emb B * ⟪emb U, emb W⟫ := by
  obtain ⟨U, hU, hmin⟩ := exists_rayleigh_minimiser emb hco hsymm hRellich hne
  exact ⟨U, hU, hmin, fun W => rayleigh_euler_lagrange emb hco hsymm hU hmin W⟩

omit [CompleteSpace V] [CompleteSpace L] in
/-- **Minimality of the principal eigenvalue.** Any nonzero weak eigenfunction has eigenvalue
at least `λ₁`. Coercivity rules out a nonzero element with vanishing image under `emb`, so the
Rayleigh bound applies. -/
theorem principalEigenvalue_le_of_weak_eigenvector (hco : IsCoercive B) {lam : ℝ} {U : V}
    (hU : U ≠ 0) (heig : ∀ W : V, B U W = lam * ⟪emb U, emb W⟫) :
    principalEigenvalue emb B ≤ lam := by
  have hUU : B U U = lam * ‖emb U‖ ^ 2 := by
    rw [heig U, real_inner_self_eq_norm_sq]
  have hnz : emb U ≠ 0 := by
    intro h0
    obtain ⟨C, hC, hcoer⟩ := id hco
    have hzero : B U U = 0 := by rw [hUU, h0]; simp
    have hUpos : 0 < ‖U‖ := norm_pos_iff.mpr hU
    nlinarith [hcoer U, mul_pos (mul_pos hC hUpos) hUpos]
  have hpos : 0 < ‖emb U‖ ^ 2 := by
    have := norm_pos_iff.mpr hnz
    positivity
  have hkey := principalEigenvalue_mul_norm_sq_le emb hco U
  rw [hUU] at hkey
  exact le_of_mul_le_mul_right hkey hpos

end EllipticPdes.Variational

namespace EllipticPdes.Sobolev

open EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ}

/-- The unit `L²` sphere of `H₀¹(Ω)`, the constraint set of the Rayleigh problem. -/
def rayleighSphere (Ω : Set (EuclideanSpace ℝ (Fin d))) : Set (H01 Ω) :=
  Variational.rayleighSphere (embL2 Ω)

/-- The values a bilinear form takes on the unit `L²` sphere. -/
def rayleighValues (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) : Set ℝ :=
  Variational.rayleighValues (embL2 Ω) B

/-- **Principal eigenvalue** of a symmetric coercive form on `H₀¹(Ω)`: the infimum of the
Rayleigh quotient `B[U, U]` over the functions of unit `L²` norm. -/
def principalEigenvalue (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) : ℝ :=
  Variational.principalEigenvalue (embL2 Ω) B

/-- A coercive form is positive semidefinite. -/
lemma nonneg_of_isCoercive (hco : IsCoercive B) (U : H01 Ω) : 0 ≤ B U U :=
  bilin_self_nonneg hco U

/-- **Rayleigh bound off the constraint set**: `λ₁‖U‖²_{L²} ≤ B[U, U]` for every `U`. -/
theorem principalEigenvalue_mul_norm_sq_le (hco : IsCoercive B) (U : H01 Ω) :
    principalEigenvalue B * ‖embL2 Ω U‖ ^ 2 ≤ B U U :=
  Variational.principalEigenvalue_mul_norm_sq_le (embL2 Ω) hco U

/-- The principal eigenvalue of a coercive form is positive. -/
theorem principalEigenvalue_pos (hco : IsCoercive B) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    0 < principalEigenvalue B :=
  Variational.principalEigenvalue_pos (embL2 Ω) hco hne

alias eq_zero_of_quadratic_nonneg := Variational.eq_zero_of_quadratic_nonneg

/-- **Euler-Lagrange equation of the Rayleigh problem.** A minimiser on the unit `L²` sphere is
a weak eigenfunction at the principal eigenvalue: `B[U, V] = λ₁⟪U, V⟫_{L²}` for every `V`. -/
theorem rayleigh_euler_lagrange (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    {U : H01 Ω} (hU : ‖embL2 Ω U‖ = 1) (hmin : B U U = principalEigenvalue B) (V : H01 Ω) :
    B U V = principalEigenvalue B * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  Variational.rayleigh_euler_lagrange (embL2 Ω) hco hsymm hU hmin V

/-- The values a form takes on the unit `L²` sphere inside a set `S`. -/
def rayleighValuesOn (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) (S : Set (H01 Ω)) : Set ℝ :=
  Variational.rayleighValuesOn (embL2 Ω) B S

/-- The infimum of the Rayleigh quotient over the unit `L²` sphere inside `S`. Taking `S` to be
the vectors `L²`-orthogonal to the earlier eigenfunctions gives the later eigenvalues. -/
def eigenvalueOn (B : H01 Ω →L[ℝ] H01 Ω →L[ℝ] ℝ) (S : Set (H01 Ω)) : ℝ :=
  Variational.eigenvalueOn (embL2 Ω) B S

/-- Positive semidefiniteness bounds the constrained values below by zero. -/
lemma rayleighValuesOn_bddBelow (hco : IsCoercive B) (S : Set (H01 Ω)) :
    BddBelow (rayleighValuesOn B S) :=
  Variational.rayleighValuesOn_bddBelow (embL2 Ω) hco S

/-- The constrained infimum is a lower bound on the constrained sphere. -/
lemma eigenvalueOn_le (hco : IsCoercive B) {S : Set (H01 Ω)} {U : H01 Ω}
    (hU : ‖embL2 Ω U‖ = 1) (hUS : U ∈ S) : eigenvalueOn B S ≤ B U U :=
  Variational.eigenvalueOn_le (embL2 Ω) hco hU hUS

/-- **Tightening the constraint raises the infimum.** -/
lemma principalEigenvalue_le_eigenvalueOn (hco : IsCoercive B) {S : Set (H01 Ω)}
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    principalEigenvalue B ≤ eigenvalueOn B S :=
  Variational.principalEigenvalue_le_eigenvalueOn (embL2 Ω) hco hne

/-- **Attainment of the infimum of the Rayleigh quotient over a weakly closed set.** Coercivity
bounds a minimising sequence, weak compactness supplies a limit, the constraint `S` passes to that
limit by hypothesis, and the Rellich compact embedding takes the unit `L²` norm to it. -/
theorem exists_rayleigh_minimiser_on (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) {S : Set (H01 Ω)}
    (hSclosed : ∀ (u : ℕ → H01 Ω) (w : H01 Ω), (∀ k, u k ∈ S) →
      (∀ v : H01 Ω, Tendsto (fun k => ⟪u k, v⟫) atTop (𝓝 ⟪w, v⟫)) → w ∈ S)
    (hne : (rayleighSphere Ω ∩ S).Nonempty) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ U ∈ S ∧ B U U = eigenvalueOn B S :=
  Variational.exists_rayleigh_minimiser_on (embL2 Ω) hco hsymm hRellich hSclosed hne

/-- **Attainment of the infimum of the Rayleigh quotient.** The unconstrained case. -/
theorem exists_rayleigh_minimiser (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ B U U = principalEigenvalue B :=
  Variational.exists_rayleigh_minimiser (embL2 Ω) hco hsymm hRellich hne

/-- **Principal eigenpair.** For a symmetric coercive form with the Rellich compact embedding
there is a `U` of unit `L²` norm attaining the infimum of the Rayleigh quotient, and it solves the
weak eigenvalue problem at that value. -/
theorem exists_principal_eigenpair (hco : IsCoercive B) (hsymm : ∀ U V : H01 Ω, B U V = B V U)
    (hRellich : IsCompactOperator (embL2 Ω)) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧ B U U = principalEigenvalue B ∧
      ∀ V : H01 Ω, B U V = principalEigenvalue B * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  Variational.exists_principal_eigenpair (embL2 Ω) hco hsymm hRellich hne

/-- **Minimality of the principal eigenvalue.** Any nonzero weak eigenfunction has eigenvalue
at least `λ₁`. -/
theorem principalEigenvalue_le_of_weak_eigen (hco : IsCoercive B) {lam : ℝ} {U : H01 Ω}
    (hU : U ≠ 0) (heig : ∀ V : H01 Ω, B U V = lam * ⟪embL2 Ω U, embL2 Ω V⟫) :
    principalEigenvalue B ≤ lam :=
  Variational.principalEigenvalue_le_of_weak_eigenvector (embL2 Ω) hco hU heig

/-! ### The Dirichlet Laplacian on a bounded measurable domain -/

/-- **Principal Dirichlet eigenvalue of `-Δ`** on a bounded measurable domain, with the compact
embedding discharged by `embL2_isCompact`. The eigenvalue of `-Δ` itself is `λ₁ - 1`, since the
graph norm on `H₀¹(Ω)` includes the function coordinate: the identity below reads
`∫ ∇u · ∇v = (λ₁ - 1) ∫ u v` once `⟪U, V⟫_{H₀¹}` is split off. -/
theorem dirichlet_principal_eigenpair (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧
      laplaceBilin Ω U U = principalEigenvalue (laplaceBilin Ω) ∧
      ∀ V : H01 Ω, laplaceBilin Ω U V
        = principalEigenvalue (laplaceBilin Ω) * ⟪embL2 Ω U, embL2 Ω V⟫ :=
  exists_principal_eigenpair (laplaceBilin_coercive Ω CP hCP hbase) (laplaceBilin_symm Ω)
    (embL2_isCompact hΩm hΩb) hne

/-- **Poincaré inequality with its optimal constant.** The principal Dirichlet eigenvalue is
the largest constant for which `λ‖u‖²_{L²} ≤ ∫ |∇u|²` on all of `H₀¹(Ω)`, since
`dirichlet_poincare_attained` produces an equality case. -/
theorem dirichlet_poincare_sharp (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (U : H01 Ω) :
    principalEigenvalue (laplaceBilin Ω) * ‖(U : H1amb Ω) 0‖ ^ 2
      ≤ ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 := by
  simpa [laplaceBilin_self] using
    principalEigenvalue_mul_norm_sq_le (laplaceBilin_coercive Ω CP hCP hbase) U

/-- The optimal Poincaré constant is attained: some `u` of unit `L²` norm has Dirichlet energy
exactly `λ₁`. -/
theorem dirichlet_poincare_attained (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖(U : H1amb Ω) 0‖ = 1 ∧
      ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 = principalEigenvalue (laplaceBilin Ω) := by
  obtain ⟨U, hU, hmin⟩ := exists_rayleigh_minimiser (laplaceBilin_coercive Ω CP hCP hbase)
    (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hne
  exact ⟨U, by simpa using hU, by simpa [laplaceBilin_self] using hmin⟩

/-- The principal Dirichlet eigenvalue is positive. -/
theorem dirichlet_principalEigenvalue_pos (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ)
    (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    0 < principalEigenvalue (laplaceBilin Ω) :=
  principalEigenvalue_pos (laplaceBilin_coercive Ω CP hCP hbase) hne

/-- **Principal Dirichlet eigenpair on a bounded domain**, with no abstract Poincaré
hypothesis: `EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded` names the constant, so
boundedness and measurability of `Ω` are the whole input. This is the statement Evans makes, and
it includes the positivity of `λ₁`. -/
theorem dirichlet_principal_eigenpair_of_bounded {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hne : ∃ V : H01 Ω, embL2 Ω V ≠ 0) :
    ∃ U : H01 Ω, ‖embL2 Ω U‖ = 1 ∧
      laplaceBilin Ω U U = principalEigenvalue (laplaceBilin Ω) ∧
      0 < principalEigenvalue (laplaceBilin Ω) ∧
      ∀ V : H01 Ω, laplaceBilin Ω U V
        = principalEigenvalue (laplaceBilin Ω) * ⟪embL2 Ω U, embL2 Ω V⟫ := by
  have hco := EllipticPdes.Poincare.laplaceBilin_coercive_of_bounded hΩb
  obtain ⟨U, hU, hmin, heq⟩ :=
    exists_principal_eigenpair hco (laplaceBilin_symm Ω) (embL2_isCompact hΩm hΩb) hne
  exact ⟨U, hU, hmin, principalEigenvalue_pos hco hne, heq⟩

end EllipticPdes.Sobolev
