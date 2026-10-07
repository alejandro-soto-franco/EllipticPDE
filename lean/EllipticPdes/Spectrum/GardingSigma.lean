/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.GardingForm
public import EllipticPdes.Spectrum.CompactSpectrum

/-!
# The exceptional set and the resolvent of an abstract Gårding form

Existence III (Evans §6.2.3, Theorem 5) for a `GardingForm V L` whose compact part `opK` is a
compact operator. Parametrising the Fredholm alternative by the shift `lam`, the set
`sigmaSet = {lam | γ/(γ+lam) is an eigenvalue of opK}` is countable with finite intersection with
every `Set.Iic C`, and `lam ∉ sigmaSet` holds exactly when the weak problem
`B[u, v] = lam ⟪emb u, emb v⟫ + ⟪f, emb v⟫` is uniquely solvable for every `f : L`
(`existence_three`). Off `sigmaSet` the resolvent is bounded (`resolvent_bound`). The reduction
is the factorisation `opAlam = opE ∘ (1 - ((γ+lam)/γ)·opK)`; eigenvalues of `opK` are positive
(coercivity of the shifted form), which bounds `sigmaSet` inside `(-γ, ∞)`.
-/

@[expose] public section

open InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.GardingForm

variable {V L : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L] (G : GardingForm V L)

/-- The exceptional set: the real `lam` for which `γ/(γ+lam)` is an eigenvalue of the compact
part `opK`; equivalently (see `notMem_sigmaSet_iff_solvable`) the `lam` for which the weak
problem `B[u, ·] = lam ⟪emb u, emb ·⟫ + f` fails to be uniquely solvable for every `f`. -/
def sigmaSet : Set ℝ :=
  {lam : ℝ | G.γ + lam ≠ 0 ∧ Module.End.HasEigenvalue G.opK.toLinearMap (G.γ / (G.γ + lam))}

/-- Eigenvalues of `opK` are positive: pairing the eigenvalue relation against the eigenvector
gives `μ B_γ[x, x] = γ ‖emb x‖²` with `B_γ[x, x] > 0` by shifted coercivity. -/
lemma opK_eigenvalue_pos {μ : ℝ} (hμ : Module.End.HasEigenvalue G.opK.toLinearMap μ)
    (hμ0 : μ ≠ 0) : 0 < μ := by
  obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
  have hKx : G.opK x = μ • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  have hEK : G.opE (G.opK x) = G.γ • G.opT x := by
    rw [opK]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  have hinner : μ * G.shifted x x = G.γ * ⟪G.emb x, G.emb x⟫ := by
    calc μ * G.shifted x x = μ * ⟪G.opE x, x⟫ := by rw [G.inner_opE]
      _ = ⟪G.opE (μ • x), x⟫ := by rw [map_smul, real_inner_smul_left]
      _ = ⟪G.opE (G.opK x), x⟫ := by rw [hKx]
      _ = G.γ * ⟪G.emb x, G.emb x⟫ := by
        rw [hEK, real_inner_smul_left, G.inner_opT]
  obtain ⟨c, hc, hcoer⟩ := G.shifted_coercive
  have hBpos : 0 < G.shifted x x := by
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
    exact lt_of_lt_of_le (by positivity) (hcoer x)
  have hμnn : 0 ≤ μ := by
    by_contra hneg
    push Not at hneg
    nlinarith [mul_neg_of_neg_of_pos hneg hBpos, G.γ_pos,
      mul_nonneg G.γ_pos.le (real_inner_self_nonneg (x := G.emb x))]
  exact lt_of_le_of_ne hμnn (Ne.symm hμ0)

/-- The Riesz operator of the `lam`-shifted weak problem:
`⟪opAlam u, v⟫ = B[u, v] - lam ⟪emb u, emb v⟫`. -/
def opAlam (lam : ℝ) : V →L[ℝ] V := (G.opE : V →L[ℝ] V) - (G.γ + lam) • G.opT

/-- Riesz identity: `⟪opAlam lam u, v⟫ = B[u, v] - lam ⟪emb u, emb v⟫`. -/
lemma inner_opAlam (lam : ℝ) (u v : V) :
    ⟪G.opAlam lam u, v⟫ = G.form u v - lam * ⟪G.emb u, G.emb v⟫ := by
  rw [opAlam, _root_.sub_apply, _root_.smul_apply, inner_sub_left, real_inner_smul_left,
    ContinuousLinearEquiv.coe_coe, G.inner_opE, G.inner_opT, G.shifted_apply]
  ring

/-- The factorisation `opAlam = opE ∘ (1 - ((γ+lam)/γ)·opK)` of the `lam`-shifted problem. -/
lemma opAlam_factor (lam : ℝ) :
    G.opAlam lam = (G.opE : V →L[ℝ] V).comp
      ((1 : V →L[ℝ] V) - ((G.γ + lam) / G.γ) • G.opK) := by
  have hγ := G.γ_pos
  refine ContinuousLinearMap.ext fun u => ?_
  simp only [opAlam, _root_.sub_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    one_apply_eq_self, map_sub, map_smul, opK, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [smul_smul, div_mul_cancel₀ _ hγ.ne']

/-- The Riesz dictionary for the `lam`-shifted problem: `u` weakly solves
`B[u, v] = lam ⟪emb u, emb v⟫ + f v` exactly when `opAlam u` is the Riesz representative
of `f`. -/
lemma opAlam_solves_iff (lam : ℝ) (f : V →L[ℝ] ℝ) (u : V) :
    (∀ v : V, G.form u v = lam * ⟪G.emb u, G.emb v⟫ + f v)
      ↔ G.opAlam lam u = (InnerProductSpace.toDual ℝ V).symm f := by
  have hg : ∀ v : V, ⟪(InnerProductSpace.toDual ℝ V).symm f, v⟫ = f v := fun v =>
    InnerProductSpace.toDual_symm_apply
  constructor
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) fun v => ?_
    rw [G.inner_opAlam, hu v, hg v]
    ring
  · intro hu v
    have h1 := G.inner_opAlam lam u v
    rw [hu, hg v] at h1
    linarith

/-- The `lam`-shifted Riesz operator is bijective off `sigmaSet`. -/
lemma opAlam_bijective_of_notMem (hK : IsCompactOperator G.opK) {lam : ℝ}
    (hlam : lam ∉ G.sigmaSet) : Function.Bijective (G.opAlam lam) := by
  have hγ := G.γ_pos
  have hEbij : Function.Bijective (G.opE : V →L[ℝ] V) := by simpa using G.opE.bijective
  by_cases hcase : G.γ + lam = 0
  · have h1 : G.opAlam lam = (G.opE : V →L[ℝ] V) := by
      rw [opAlam, hcase]
      module
    rwa [h1]
  · have hnoteig : ¬ Module.End.HasEigenvalue G.opK.toLinearMap (((G.γ + lam) / G.γ)⁻¹) := by
      rw [inv_div]
      exact fun h => hlam ⟨hcase, h⟩
    rw [G.opAlam_factor lam]
    exact hEbij.comp (hK.bijective_one_sub_smul (div_ne_zero hcase hγ.ne') hnoteig)

/-- A point of `sigmaSet` defeats uniqueness already for `f = 0`: the eigenvector of `opK` at
`γ/(γ+lam)` is a nonzero weak solution of the homogeneous `lam`-problem. -/
lemma not_unique_of_mem_sigmaSet {lam : ℝ} (hlam : lam ∈ G.sigmaSet) :
    ¬ ∃! u : V, ∀ v : V, G.form u v = lam * ⟪G.emb u, G.emb v⟫ := by
  obtain ⟨hne, heig⟩ := hlam
  obtain ⟨x, hx_mem, hx_ne⟩ := heig.exists_hasEigenvector
  have hγ := G.γ_pos
  have hKx : G.opK x = (G.γ / (G.γ + lam)) • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  have hAx : G.opAlam lam x = 0 := by
    rw [G.opAlam_factor lam, ContinuousLinearMap.comp_apply]
    have h0 : ((1 : V →L[ℝ] V) - ((G.γ + lam) / G.γ) • G.opK) x = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self, _root_.smul_apply, hKx, smul_smul,
        show (G.γ + lam) / G.γ * (G.γ / (G.γ + lam)) = 1 by field_simp, one_smul, sub_self]
    rw [h0, map_zero]
  have hxsol : ∀ v : V, G.form x v = lam * ⟪G.emb x, G.emb v⟫ := fun v => by
    have h1 := G.inner_opAlam lam x v
    rw [hAx, inner_zero_left] at h1
    linarith
  rintro ⟨u, -, huniq⟩
  exact hx_ne (by rw [huniq x hxsol, huniq 0 fun v => by simp])

/-- Off `sigmaSet`, the `lam`-shifted weak problem is uniquely solvable for every functional. -/
theorem solvable_of_notMem_sigmaSet (hK : IsCompactOperator G.opK) {lam : ℝ}
    (hlam : lam ∉ G.sigmaSet) (f : V →L[ℝ] ℝ) :
    ∃! u : V, ∀ v : V, G.form u v = lam * ⟪G.emb u, G.emb v⟫ + f v :=
  (existsUnique_congr fun u => (G.opAlam_solves_iff lam f u).symm).mp
    ((G.opAlam_bijective_of_notMem hK hlam).existsUnique ((InnerProductSpace.toDual ℝ V).symm f))

/-- The membership characterisation of `sigmaSet`: `lam ∉ sigmaSet` exactly when
`B[u, v] = lam ⟪emb u, emb v⟫ + f v` is uniquely solvable for every functional `f`. -/
theorem notMem_sigmaSet_iff_solvable (hK : IsCompactOperator G.opK) (lam : ℝ) :
    lam ∉ G.sigmaSet ↔
      ∀ f : V →L[ℝ] ℝ, ∃! u : V, ∀ v : V, G.form u v = lam * ⟪G.emb u, G.emb v⟫ + f v := by
  refine ⟨fun h f => G.solvable_of_notMem_sigmaSet hK h f, fun hall hmem => ?_⟩
  refine G.not_unique_of_mem_sigmaSet hmem ?_
  refine (existsUnique_congr fun u => forall_congr' fun v => ?_).mp (hall 0)
  simp

/-- On `sigmaSet`, `γ + lam` is positive: eigenvalues of `opK` are positive. -/
lemma pos_of_mem_sigmaSet {lam : ℝ} (hlam : lam ∈ G.sigmaSet) : 0 < G.γ + lam := by
  obtain ⟨hne, heig⟩ := hlam
  have hμpos := G.opK_eigenvalue_pos heig (div_ne_zero G.γ_pos.ne' hne)
  by_contra hneg
  push Not at hneg
  linarith [div_nonpos_of_nonneg_of_nonpos G.γ_pos.le hneg]

/-- Bounded-above slices of `sigmaSet` are finite: a `lam ∈ sigmaSet ∩ Iic C` has
`γ/(γ+lam) ≥ γ/(γ+C) > 0`, and only finitely many such eigenvalues of `opK` exist. -/
theorem sigmaSet_inter_Iic_finite (hK : IsCompactOperator G.opK) (C : ℝ) :
    (G.sigmaSet ∩ Set.Iic C).Finite := by
  have hγ := G.γ_pos
  by_cases hC : G.γ + C ≤ 0
  · convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro lam ⟨hmem, hle⟩
    linarith [G.pos_of_mem_sigmaSet hmem, Set.mem_Iic.mp hle]
  · push Not at hC
    set δ : ℝ := G.γ / (G.γ + C) with hδdef
    have hδ : 0 < δ := div_pos hγ hC
    have himg : (fun lam => G.γ / (G.γ + lam)) '' (G.sigmaSet ∩ Set.Iic C) ⊆
        {μ : ℝ | Module.End.HasEigenvalue G.opK.toLinearMap μ ∧ δ ≤ ‖μ‖} := by
      rintro _ ⟨lam, ⟨hmem, hle⟩, rfl⟩
      have hpos := G.pos_of_mem_sigmaSet hmem
      refine ⟨hmem.2, ?_⟩
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hγ hpos), hδdef]
      gcongr
      exact Set.mem_Iic.mp hle
    refine Set.Finite.of_finite_image ((hK.finite_setOf_hasEigenvalue_norm_ge hδ).subset himg) ?_
    rintro lam1 hlam1 lam2 hlam2 heq
    have hpos1 := G.pos_of_mem_sigmaSet hlam1.1
    have hpos2 := G.pos_of_mem_sigmaSet hlam2.1
    rw [div_eq_div_iff hpos1.ne' hpos2.ne'] at heq
    linarith [mul_left_cancel₀ hγ.ne' heq]

/-- The exceptional set is countable: finite on each bounded slice `sigmaSet ∩ Iic n`. -/
theorem sigmaSet_countable (hK : IsCompactOperator G.opK) : G.sigmaSet.Countable := by
  refine Set.Countable.mono (fun lam hlam => ?_)
    (Set.countable_iUnion fun n : ℕ => (G.sigmaSet_inter_Iic_finite hK n).countable)
  obtain ⟨n, hn⟩ := exists_nat_ge lam
  exact Set.mem_iUnion.mpr ⟨n, hlam, hn⟩

/-- The functional `v ↦ ⟪f, emb v⟫` on `V` determined by a right-hand side `f : L`. -/
def pairing (f : L) : V →L[ℝ] ℝ := (innerSL ℝ f).comp G.emb

/-- `pairing f v = ⟪f, emb v⟫`. -/
@[simp] lemma pairing_apply (f : L) (v : V) : G.pairing f v = ⟪f, G.emb v⟫ := rfl

/-- The functional `pairing f` has norm at most `‖f‖ ‖emb‖`. -/
lemma norm_pairing_le (f : L) : ‖G.pairing f‖ ≤ ‖f‖ * ‖G.emb‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (innerSL_apply_norm (𝕜 := ℝ) f).le (norm_nonneg _))

/-- **Existence III.** The exceptional set is countable, has finite intersection with every
`(-∞, C]` (so an infinite one is a nondecreasing sequence diverging to `+∞`), and `lam` lies
outside it exactly when `B[u, v] = lam ⟪emb u, emb v⟫ + ⟪f, emb v⟫` has a unique solution for
every `f : L`. -/
theorem existence_three (hK : IsCompactOperator G.opK) :
    G.sigmaSet.Countable ∧ (∀ C : ℝ, (G.sigmaSet ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ G.sigmaSet ↔ ∀ f : L, ∃! u : V, ∀ v : V,
        G.form u v = lam * ⟪G.emb u, G.emb v⟫ + ⟪f, G.emb v⟫ := by
  refine ⟨G.sigmaSet_countable hK, G.sigmaSet_inter_Iic_finite hK, fun lam => ⟨fun h f => ?_,
    fun hall => ?_⟩⟩
  · exact G.solvable_of_notMem_sigmaSet hK h (G.pairing f)
  · intro hmem
    refine G.not_unique_of_mem_sigmaSet hmem ?_
    refine (existsUnique_congr fun u => forall_congr' fun v => ?_).mp (hall 0)
    simp

/-- **Boundedness of the resolvent.** For `lam ∉ sigmaSet` there is `C > 0` such that every weak
solution `u` of `B[u, v] = lam ⟪emb u, emb v⟫ + ⟪f, emb v⟫` satisfies `‖emb u‖ ≤ C ‖f‖`. The
constant is built from the operator norm of the inverse of the `lam`-shifted Riesz operator. -/
theorem resolvent_bound (hK : IsCompactOperator G.opK) {lam : ℝ} (hlam : lam ∉ G.sigmaSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : L) (u : V),
      (∀ v : V, G.form u v = lam * ⟪G.emb u, G.emb v⟫ + ⟪f, G.emb v⟫) →
        ‖G.emb u‖ ≤ C * ‖f‖ := by
  obtain ⟨w, hw⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr
    (G.opAlam_bijective_of_notMem hK hlam)
  set B : V →L[ℝ] V := ↑w⁻¹ with hBdef
  have hBA : ∀ y : V, B (G.opAlam lam y) = y := fun y => by
    have h1 : B * G.opAlam lam = 1 := by rw [hBdef, ← hw]; exact w.inv_mul
    simpa using congrArg (fun T : V →L[ℝ] V => T y) h1
  refine ⟨‖G.emb‖ ^ 2 * ‖B‖ + 1, by positivity, fun f u hu => ?_⟩
  have hAu : G.opAlam lam u = (InnerProductSpace.toDual ℝ V).symm (G.pairing f) :=
    (G.opAlam_solves_iff lam (G.pairing f) u).mp hu
  have hub : ‖u‖ ≤ ‖B‖ * (‖f‖ * ‖G.emb‖) :=
    calc ‖u‖ = ‖B (G.opAlam lam u)‖ := by rw [hBA u]
      _ ≤ ‖B‖ * ‖G.opAlam lam u‖ := B.le_opNorm _
      _ = ‖B‖ * ‖G.pairing f‖ := by rw [hAu, LinearIsometryEquiv.norm_map]
      _ ≤ ‖B‖ * (‖f‖ * ‖G.emb‖) := by gcongr; exact G.norm_pairing_le f
  calc ‖G.emb u‖ ≤ ‖G.emb‖ * ‖u‖ := G.emb.le_opNorm u
    _ ≤ ‖G.emb‖ * (‖B‖ * (‖f‖ * ‖G.emb‖)) := by gcongr
    _ = (‖G.emb‖ ^ 2 * ‖B‖) * ‖f‖ := by ring
    _ ≤ (‖G.emb‖ ^ 2 * ‖B‖ + 1) * ‖f‖ := by gcongr; linarith

end EllipticPdes.GardingForm
