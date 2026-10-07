/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.FredholmComplete
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Spectrum of compact operators and Existence III

Two layers.

**Generic** (Evans Appendix D.5, Theorem 6: the spectrum of a compact operator `K` on a
real Hilbert space): `0 ∈ σ(K)` when the space is infinite-dimensional; away from zero
the spectrum consists of eigenvalues (mathlib's Fredholm alternative); and the
eigenvalues cannot accumulate away from zero: for every `δ > 0` only finitely many
eigenvalues have `|μ| ≥ δ`, so `σ(K) \ {0}` is countable. The accumulation argument is
the classical eigenvector chain: distinct eigenvalues give a strictly increasing chain
of spans `Eₙ`, Hilbert geometry provides unit vectors `uₙ ∈ Eₙ₊₁ ∩ Eₙᗮ`, and
`(μₙ - K)Eₙ₊₁ ⊆ Eₙ` forces `‖K(uₙ/μₙ) - K(uₘ/μₘ)‖ ≥ 1` for `m < n`, contradicting
the compactness of `K` on the bounded sequence `uₙ/μₙ`.

**Elliptic** (`Existence III`, obtained by parametrising the Fredholm alternative of
Evans §6.2.3 by the shift `λ` and invoking the spectral theorem of Evans Appendix D.5):
the set `Σ = {λ : γ/(γ+λ) is an eigenvalue of opK}` is countable with finite
intersections with every `Set.Iic C` (so an infinite `Σ` is a sequence increasing to
`+∞`), and `λ ∉ Σ` holds exactly when the weak problem `Lu = λu + f` is uniquely
solvable for every right-hand side. The reduction is the `opK` factorisation of
`Fredholm.lean`, shifted: `opAlam = opE ∘ (1 - ((γ+λ)/γ)·opK)`. Eigenvalues of `opK`
are positive (coercivity of the shifted form), which bounds `Σ` inside `(-γ, ∞)`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

/-! ### Spectrum of a compact operator (Evans Appendix D.5, Theorem 6) -/

section CompactSpectrum

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

open Module in
/-- In a linearly independent family, the span of the first `n + 1` vectors contains a unit
vector orthogonal to the span of the first `n`. -/
theorem LinearIndependent.exists_unit_mem_span_succ_orthogonal {e : ℕ → E}
    (hli : LinearIndependent 𝕜 e) (n : ℕ) :
    ∃ u ∈ Submodule.span 𝕜 (e '' Set.Iio (n + 1)),
      u ∈ (Submodule.span 𝕜 (e '' Set.Iio n))ᗮ ∧ ‖u‖ = 1 := by
  set S := Submodule.span 𝕜 (e '' Set.Iio n)
  have : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 ((Set.finite_Iio n).image e)
  have hmem : e n ∈ Submodule.span 𝕜 (e '' Set.Iio (n + 1)) :=
    Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩
  have hS : S ≤ Submodule.span 𝕜 (e '' Set.Iio (n + 1)) :=
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio n.le_succ))
  have hw : e n - S.starProjection (e n) ≠ 0 := fun h0 => by
    refine hli.notMem_span_image (s := Set.Iio n) (x := n) (by simp) ?_
    rw [sub_eq_zero.mp h0]
    exact S.starProjection_apply_mem _
  refine ⟨(‖e n - S.starProjection (e n)‖⁻¹ : 𝕜) • (e n - S.starProjection (e n)),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem (hS (S.starProjection_apply_mem _))),
    Submodule.smul_mem _ _ (S.sub_starProjection_mem_orthogonal _), ?_⟩
  exact norm_smul_inv_norm hw

/-- A unit vector orthogonal to `z` is at distance at least `1` from `z`. -/
theorem one_le_norm_sub_of_inner_eq_zero {u z : E} (hu : ‖u‖ = 1) (h : inner 𝕜 u z = 0) :
    1 ≤ ‖u - z‖ := by
  have hsq := norm_sub_sq (𝕜 := 𝕜) u z
  rw [hu, h, map_zero] at hsq
  nlinarith [norm_nonneg (u - z), sq_nonneg ‖z‖]

/-- Separation along an invariant flag. Let `S n` be an increasing family of subspaces
invariant under `K` with `(μ n - K) (S (n + 1)) ⊆ S n`, and let `u n` be unit vectors in
`S (n + 1)` orthogonal to `S n`. Then the images `K (u n / μ n)` are pairwise at distance
at least `1`. -/
theorem Module.End.one_le_norm_apply_sub_of_flag {K : E →ₗ[𝕜] E} {μ : ℕ → 𝕜}
    (hμ : ∀ n, μ n ≠ 0) {S : ℕ → Submodule 𝕜 E} (hmono : Monotone S)
    (hK : ∀ n, ∀ x ∈ S n, K x ∈ S n) (hshift : ∀ n, ∀ x ∈ S (n + 1), μ n • x - K x ∈ S n)
    {u : ℕ → E} (hu : ∀ n, u n ∈ S (n + 1) ∧ u n ∈ (S n)ᗮ ∧ ‖u n‖ = 1) {m n : ℕ}
    (hmn : m < n) :
    1 ≤ ‖K ((μ n)⁻¹ • u n) - K ((μ m)⁻¹ • u m)‖ := by
  set z : E := (μ n)⁻¹ • (μ n • u n - K (u n)) + K ((μ m)⁻¹ • u m)
  have hz : z ∈ S n := Submodule.add_mem _ (Submodule.smul_mem _ _ (hshift n _ (hu n).1))
    (hmono (Nat.succ_le_of_lt hmn) (by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (hK _ _ (hu m).1)))
  have hdiff : K ((μ n)⁻¹ • u n) - K ((μ m)⁻¹ • u m) = u n - z := by
    simp only [z, map_smul, smul_sub, smul_smul, inv_mul_cancel₀ (hμ n), one_smul]
    abel
  rw [hdiff]
  exact one_le_norm_sub_of_inner_eq_zero (𝕜 := 𝕜) (hu n).2.2
    ((Submodule.mem_orthogonal' (S n) (u n)).mp (hu n).2.1 z hz)

/-- A compact operator maps a bounded sequence to a sequence with two terms less than `1`
apart. -/
theorem IsCompactOperator.exists_norm_sub_lt_one {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {K : E →ₗ[𝕜] F} (hK : IsCompactOperator K) {R : ℝ} {v : ℕ → E}
    (hv : ∀ n, ‖v n‖ ≤ R) : ∃ m n, m < n ∧ ‖K (v n) - K (v m)‖ < 1 := by
  have hmem : ∀ n, K (v n) ∈ closure (K '' Metric.closedBall 0 R) := fun n =>
    subset_closure ⟨v n, by simpa using hv n, rfl⟩
  obtain ⟨_, _, φ, hφ, hlim⟩ := (hK.isCompact_closure_image_closedBall R).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (Filter.Tendsto.cauchySeq hlim) 1 one_pos
  exact ⟨φ N, φ (N + 1), hφ N.lt_succ_self,
    by simpa [dist_eq_norm, Function.comp] using hN (N + 1) N.le_succ N le_rfl⟩

/-- The eigenvector flag of an injective sequence of eigenvalues: the span of the first `n`
eigenvectors is `K`-invariant, and `μ n - K` maps the span of the first `n + 1` into the span of
the first `n`. -/
theorem Module.End.span_flag_of_hasEigenvector {K : E →ₗ[𝕜] E} {μ : ℕ → 𝕜} {e : ℕ → E}
    (he : ∀ n, Module.End.HasEigenvector K (μ n) (e n)) (n : ℕ) :
    (∀ x ∈ Submodule.span 𝕜 (e '' Set.Iio n), K x ∈ Submodule.span 𝕜 (e '' Set.Iio n)) ∧
    ∀ x ∈ Submodule.span 𝕜 (e '' Set.Iio (n + 1)),
      μ n • x - K x ∈ Submodule.span 𝕜 (e '' Set.Iio n) := by
  have hKe : ∀ i, K (e i) = μ i • e i := fun i => Module.End.mem_eigenspace_iff.mp (he i).1
  have hmem : ∀ i < n, e i ∈ Submodule.span 𝕜 (e '' Set.Iio n) := fun i hi =>
    Submodule.subset_span ⟨i, hi, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · refine (Submodule.map_span_le K _ _).mpr ?_ (Submodule.mem_map_of_mem hx)
    rintro _ ⟨i, hi, rfl⟩
    rw [hKe]
    exact Submodule.smul_mem _ _ (hmem i hi)
  · let L : E →ₗ[𝕜] E := μ n • LinearMap.id - K
    refine (Submodule.map_span_le L _ _).mpr ?_ (Submodule.mem_map_of_mem hx)
    rintro _ ⟨i, hi, rfl⟩
    have : L (e i) = (μ n - μ i) • e i := by simp [L, hKe, sub_smul]
    rw [this]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact Submodule.smul_mem _ _ (hmem i h)
    · simp

/-- **Eigenvalues of a compact operator do not accumulate away from zero**: for every
`δ > 0` there are only finitely many eigenvalues `μ` with `δ ≤ ‖μ‖`. The classical
eigenvector-chain argument, with the Riesz lemma replaced by Hilbert orthogonality. -/
theorem IsCompactOperator.finite_setOf_hasEigenvalue_norm_ge {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) {δ : ℝ} (hδ : 0 < δ) :
    {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ ∧ δ ≤ ‖μ‖}.Finite := by
  by_contra hcon
  set emb := (Set.not_finite.mp hcon).natEmbedding
  set μ : ℕ → 𝕜 := fun n => (emb n : 𝕜)
  have hprop : ∀ n, Module.End.HasEigenvalue K.toLinearMap (μ n) ∧ δ ≤ ‖μ n‖ := fun n => (emb n).2
  have hμne : ∀ n, μ n ≠ 0 := fun n h0 => by
    have := (hprop n).2
    rw [h0, norm_zero] at this
    linarith
  choose e he using fun n => (hprop n).1.exists_hasEigenvector
  have hli : LinearIndependent 𝕜 e := Module.End.eigenvectors_linearIndependent' K.toLinearMap μ
    (fun a b hab => emb.injective (Subtype.coe_injective hab)) e he
  choose u hu1 hu2 hu3 using hli.exists_unit_mem_span_succ_orthogonal
  have hmono : Monotone fun n => Submodule.span 𝕜 (e '' Set.Iio n) := fun m n hmn =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))
  obtain ⟨m, n, hmn, hlt⟩ := hK.exists_norm_sub_lt_one (K := K.toLinearMap)
    (v := fun n => (μ n)⁻¹ • u n) (R := δ⁻¹) fun n => by
      rw [norm_smul, norm_inv, hu3, mul_one]
      exact inv_anti₀ hδ (hprop n).2
  exact absurd hlt (not_lt.mpr (Module.End.one_le_norm_apply_sub_of_flag hμne hmono
    (fun n => (Module.End.span_flag_of_hasEigenvector he n).1)
    (fun n => (Module.End.span_flag_of_hasEigenvector he n).2)
    (fun n => ⟨hu1 n, hu2 n, hu3 n⟩) hmn))

variable {K : E →L[𝕜] E}

/-- The nonzero eigenvalues of a compact operator form a countable set: the union of
the finite slices `{δ ≤ ‖μ‖}` over `δ = 1/(n+1)`. -/
theorem IsCompactOperator.countable_setOf_hasEigenvalue_ne_zero (hK : IsCompactOperator K) :
    {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ ∧ μ ≠ 0}.Countable := by
  refine Set.Countable.mono (fun μ ⟨hμ, hμ0⟩ => ?_) (Set.countable_iUnion fun n : ℕ =>
    (hK.finite_setOf_hasEigenvalue_norm_ge (δ := 1 / (n + 1)) (by positivity)).countable)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hμ0)
  exact Set.mem_iUnion.mpr ⟨n, hμ, hn.le⟩

/-- `0` lies in the spectrum of a compact operator on an infinite-dimensional space: an
inverse would make the identity compact (Evans Appendix D.5, Theorem 6(i)). -/
theorem IsCompactOperator.zero_mem_spectrum (hK : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional 𝕜 E) : (0 : 𝕜) ∈ spectrum 𝕜 K := by
  rw [spectrum.zero_mem_iff]
  intro hunit
  obtain ⟨w, hw⟩ := hunit
  refine hinf ((isCompactOperator_id_iff_finiteDimensional (𝕜 := 𝕜)).mp ?_)
  have := hK.clm_comp (↑w⁻¹ : E →L[𝕜] E)
  rwa [← hw, ← ContinuousLinearMap.coe_comp, ← ContinuousLinearMap.mul_def, w.inv_mul] at this

/-- Away from zero the spectrum of a compact operator consists exactly of the eigenvalues
(Evans Appendix D.5, Theorem 6(ii)), mathlib's Fredholm alternative as a set identity. -/
theorem IsCompactOperator.spectrum_diff_zero_eq [CompleteSpace E] (hK : IsCompactOperator K) :
    spectrum 𝕜 K \ {0} = {μ : 𝕜 | Module.End.HasEigenvalue K.toLinearMap μ} \ {0} := by
  ext μ
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  exact and_congr_left fun h0 => (hK.hasEigenvalue_iff_mem_spectrum h0).symm

end CompactSpectrum

namespace EllipticPdes.Sobolev

section CompactSpectrum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E}

/-- **Spectrum of a compact operator (Evans Appendix D.5, Theorem 6).** On an
infinite-dimensional real Hilbert space, a compact operator `K` has `0` in its real
spectrum; away from zero the spectrum consists exactly of the eigenvalues; the nonzero
spectrum is countable; and only finitely many spectral points have `|μ| ≥ δ` for each
`δ > 0`, so an enumeration of the nonzero spectrum converges to `0`. -/
theorem spectrum_compact_operator (hK : IsCompactOperator K)
    (hinf : ¬ FiniteDimensional ℝ E) :
    (0 : ℝ) ∈ spectrum ℝ K
    ∧ spectrum ℝ K \ {0}
        = {μ : ℝ | Module.End.HasEigenvalue (K.toLinearMap) μ} \ {0}
    ∧ (spectrum ℝ K \ {0}).Countable
    ∧ ∀ δ : ℝ, 0 < δ → {μ ∈ spectrum ℝ K | δ ≤ |μ|}.Finite := by
  refine ⟨hK.zero_mem_spectrum hinf, hK.spectrum_diff_zero_eq, ?_, fun δ hδ => ?_⟩
  · refine hK.countable_setOf_hasEigenvalue_ne_zero.mono ?_
    rw [hK.spectrum_diff_zero_eq]
    exact fun μ ⟨hμ, h0⟩ => ⟨hμ, h0⟩
  · refine (hK.finite_setOf_hasEigenvalue_norm_ge hδ).subset fun μ ⟨hmem, habs⟩ => ?_
    have h0 : μ ≠ 0 := by
      rintro rfl
      simp at habs
      linarith
    exact ⟨(hK.hasEigenvalue_iff_mem_spectrum h0).mpr hmem, by simpa using habs⟩

end CompactSpectrum

/-! ### Existence III for the elliptic problem -/

namespace FullEllipticOp

variable {d : ℕ} (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- **Set `Σ` of Existence III**: the real `λ` for which `γ/(γ+λ)` is an
eigenvalue of the compact part `opK` of the reduction, equivalently (see
`notMem_sigmaSet_iff_solvable`), the `λ` for which the weak problem `Lu = λu + f`
fails to be uniquely solvable for every right-hand side. -/
def sigmaSet : Set ℝ :=
  {lam : ℝ | Op.gardingγ + lam ≠ 0
    ∧ Module.End.HasEigenvalue (Op.opK Ω).toLinearMap
        (Op.gardingγ / (Op.gardingγ + lam))}

/-- Eigenvalues of `opK` are positive: pairing the eigenvalue relation against the
eigenvector gives `μ B_γ[x,x] = γ ‖x₀‖²` with `B_γ[x,x] > 0` by shifted coercivity. -/
lemma opK_eigenvalue_pos {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (Op.opK Ω).toLinearMap μ) (hμ0 : μ ≠ 0) : 0 < μ := by
  obtain ⟨x, hx_mem, hx_ne⟩ := hμ.exists_hasEigenvector
  have hKx : Op.opK Ω x = μ • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  -- `opE (opK x) = γ • opT x`
  have hEK : (Op.opE Ω) (Op.opK Ω x) = Op.gardingγ • opT Ω x := by
    rw [opK]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  -- pair against `x`
  have hinner : μ * Op.shiftedBilin Ω Op.gardingγ x x
      = Op.gardingγ * zerothForm Ω x x := by
    calc μ * Op.shiftedBilin Ω Op.gardingγ x x
        = μ * ⟪(Op.opE Ω) x, x⟫ := by rw [Op.inner_opE Ω]
      _ = ⟪μ • (Op.opE Ω) x, x⟫ := (real_inner_smul_left _ _ _).symm
      _ = ⟪(Op.opE Ω) (μ • x), x⟫ := by rw [map_smul]
      _ = ⟪(Op.opE Ω) (Op.opK Ω x), x⟫ := by rw [hKx]
      _ = ⟪Op.gardingγ • opT Ω x, x⟫ := by rw [hEK]
      _ = Op.gardingγ * ⟪opT Ω x, x⟫ := real_inner_smul_left (opT Ω x) x Op.gardingγ
      _ = Op.gardingγ * zerothForm Ω x x := by rw [inner_opT Ω]
  obtain ⟨c, hc, hcoer⟩ := Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hBpos : 0 < Op.shiftedBilin Ω Op.gardingγ x x := by
    have h2 : 0 < c * ‖x‖ * ‖x‖ := by positivity
    exact lt_of_lt_of_le h2 (hcoer x)
  have hn0 : 0 ≤ zerothForm Ω x x := by
    rw [zerothForm_apply]
    exact real_inner_self_nonneg
  have hγ := Op.gardingγ_pos
  have hμnn : 0 ≤ μ := by
    by_contra hneg
    push Not at hneg
    have hlt : μ * Op.shiftedBilin Ω Op.gardingγ x x < 0 :=
      mul_neg_of_neg_of_pos hneg hBpos
    have hge : 0 ≤ Op.gardingγ * zerothForm Ω x x :=
      mul_nonneg hγ.le hn0
    linarith [hinner]
  exact lt_of_le_of_ne hμnn (Ne.symm hμ0)

/-- The Riesz operator of the `λ`-shifted weak problem: `⟪opAlam u, v⟫ = B[u,v] - λ⟨u₀,v₀⟩`. -/
def opAlam (lam : ℝ) : H01 Ω →L[ℝ] H01 Ω :=
  (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - (Op.gardingγ + lam) • opT Ω

/-- Riesz identity: `⟪Op.opAlam Ω lam u, v⟫ = B[u, v] - lam · zerothForm Ω u v`. -/
lemma inner_opAlam (lam : ℝ) (u v : H01 Ω) :
    ⟪Op.opAlam Ω lam u, v⟫ = Op.fullBilin Ω u v - lam * zerothForm Ω u v := by
  rw [opAlam, _root_.sub_apply, _root_.smul_apply,
    inner_sub_left, real_inner_smul_left, ContinuousLinearEquiv.coe_coe, Op.inner_opE Ω,
    inner_opT Ω, Op.shiftedBilin_apply, zerothForm_apply]
  ring

/-- The factorisation `opAlam = opE ∘ (1 - ((γ+λ)/γ)·opK)` of the `λ`-shifted problem. -/
lemma opAlam_factor (lam : ℝ) :
    Op.opAlam Ω lam = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp
      ((1 : H01 Ω →L[ℝ] H01 Ω)
        - ((Op.gardingγ + lam) / Op.gardingγ) • Op.opK Ω) := by
  have hγ := Op.gardingγ_pos
  refine ContinuousLinearMap.ext (fun u => ?_)
  simp only [opAlam, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self, map_sub, map_smul, opK,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [smul_smul, div_mul_cancel₀ _ hγ.ne']

/-- The Riesz dictionary for the `λ`-shifted problem: `u` weakly solves
`B[u,v] = λ⟨u₀,v₀⟩ + f(v)` exactly when `opAlam u` is the Riesz representative of `f`. -/
lemma opAlam_solves_iff (lam : ℝ) (f : H01 Ω →L[ℝ] ℝ) (u : H01 Ω) :
    (∀ v : H01 Ω, Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v)
      ↔ Op.opAlam Ω lam u = (InnerProductSpace.toDual ℝ (H01 Ω)).symm f := by
  have hgrep : ∀ v : H01 Ω, ⟪(InnerProductSpace.toDual ℝ (H01 Ω)).symm f, v⟫ = f v :=
    fun v => InnerProductSpace.toDual_symm_apply
  constructor
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opAlam Ω, hu v, hgrep v]
    ring
  · intro hu v
    have h1 := Op.inner_opAlam Ω lam u v
    rw [hu, hgrep v] at h1
    linarith [h1]

/-- The `λ`-shifted Riesz operator is bijective off `Σ`. -/
lemma opAlam_bijective_of_notMem (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) : Function.Bijective (Op.opAlam Ω lam) := by
  have hγ := Op.gardingγ_pos
  by_cases hcase : Op.gardingγ + lam = 0
  · -- `λ = -γ`: the problem is the coercive shifted one, `opAlam = opE`
    have h1 : Op.opAlam Ω lam = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) := by
      rw [opAlam, hcase]
      module
    rw [h1]
    simpa using (Op.opE Ω).bijective
  · -- otherwise: the Fredholm alternative at `μ = γ/(γ+λ) ≠ 0`
    have hnoteig : ¬ Module.End.HasEigenvalue (Op.opK Ω).toLinearMap
        (((Op.gardingγ + lam) / Op.gardingγ)⁻¹) := by
      rw [inv_div]
      exact fun h => hlam ⟨hcase, h⟩
    have h1bij := hK.bijective_one_sub_smul (div_ne_zero hcase hγ.ne') hnoteig
    have hEbij : Function.Bijective (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) := by
      simpa using (Op.opE Ω).bijective
    rw [Op.opAlam_factor Ω lam]
    exact hEbij.comp h1bij

/-- A point of `Σ` defeats uniqueness already for `f = 0`: the eigenvector of `opK` at
`γ/(γ+λ)` is a nonzero weak solution of the homogeneous `λ`-problem. -/
lemma not_unique_of_mem_sigmaSet {lam : ℝ} (hlam : lam ∈ Op.sigmaSet Ω) :
    ¬ ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = lam * zerothForm Ω u v := by
  obtain ⟨hne, heig⟩ := hlam
  obtain ⟨x, hx_mem, hx_ne⟩ := heig.exists_hasEigenvector
  have hγ := Op.gardingγ_pos
  have hKx : Op.opK Ω x = (Op.gardingγ / (Op.gardingγ + lam)) • x := by
    simpa using Module.End.mem_eigenspace_iff.mp hx_mem
  -- `opAlam x = 0`
  have hAx : Op.opAlam Ω lam x = 0 := by
    rw [Op.opAlam_factor Ω lam, ContinuousLinearMap.comp_apply]
    have h0 : ((1 : H01 Ω →L[ℝ] H01 Ω)
        - ((Op.gardingγ + lam) / Op.gardingγ) • Op.opK Ω) x = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self,
        _root_.smul_apply, hKx, smul_smul]
      rw [show (Op.gardingγ + lam) / Op.gardingγ * (Op.gardingγ / (Op.gardingγ + lam))
          = 1 by field_simp]
      rw [one_smul, sub_self]
    rw [h0, map_zero]
  -- `x` solves the homogeneous problem
  have hxsol : ∀ v : H01 Ω, Op.fullBilin Ω x v = lam * zerothForm Ω x v := by
    intro v
    have h1 := Op.inner_opAlam Ω lam x v
    rw [hAx, inner_zero_left] at h1
    linarith [h1]
  -- `0` solves it too
  have h0sol : ∀ v : H01 Ω, Op.fullBilin Ω (0 : H01 Ω) v
      = lam * zerothForm Ω (0 : H01 Ω) v := by
    intro v
    simp
  rintro ⟨u, -, huniq⟩
  exact hx_ne (by rw [huniq x hxsol, huniq 0 h0sol])

/-- Off `Σ`, the `λ`-shifted weak problem is uniquely solvable for every functional. -/
theorem solvable_of_notMem_sigmaSet (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω,
      Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v := by
  have hbij := Op.opAlam_bijective_of_notMem Ω hK hlam
  exact (existsUnique_congr (fun u =>
    (Op.opAlam_solves_iff Ω lam f u).symm)).mp
    (hbij.existsUnique ((InnerProductSpace.toDual ℝ (H01 Ω)).symm f))

/-- The membership characterisation of `Σ` (the `H⁻¹` form of Existence III(i)):
`λ ∉ Σ` exactly when `B[u,v] = λ⟨u₀,v₀⟩ + f(v)` is uniquely solvable for every `f`. -/
theorem notMem_sigmaSet_iff_solvable (hK : IsCompactOperator (Op.opK Ω)) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω
      ↔ ∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω,
          Op.fullBilin Ω u v = lam * zerothForm Ω u v + f v := by
  constructor
  · exact fun h f => Op.solvable_of_notMem_sigmaSet Ω hK h f
  · intro hall
    by_contra hmem
    apply Op.not_unique_of_mem_sigmaSet Ω hmem
    have h0 := hall 0
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h0
    simp

/-- Bounded-above slices of `Σ` are finite: a `λ ∈ Σ ∩ Iic C` has
`μ(λ) = γ/(γ+λ) ≥ γ/(γ+C) > 0` (positivity of the `opK` eigenvalues bounds `Σ`
inside `(-γ, ∞)`), and only finitely many such eigenvalues exist. -/
theorem sigmaSet_inter_Iic_finite (hK : IsCompactOperator (Op.opK Ω)) (C : ℝ) :
    (Op.sigmaSet Ω ∩ Set.Iic C).Finite := by
  have hγ := Op.gardingγ_pos
  -- `γ + λ > 0` on `Σ`
  have hposmem : ∀ lam ∈ Op.sigmaSet Ω, 0 < Op.gardingγ + lam := by
    rintro lam ⟨hne, heig⟩
    have hμpos : 0 < Op.gardingγ / (Op.gardingγ + lam) :=
      Op.opK_eigenvalue_pos Ω heig (div_ne_zero hγ.ne' hne)
    by_contra hneg
    push Not at hneg
    have h2 : Op.gardingγ / (Op.gardingγ + lam) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hγ.le hneg
    linarith
  by_cases hC : Op.gardingγ + C ≤ 0
  · convert Set.finite_empty
    rw [Set.eq_empty_iff_forall_notMem]
    rintro lam ⟨hmem, hle⟩
    have h1 := hposmem lam hmem
    rw [Set.mem_Iic] at hle
    linarith
  · push Not at hC
    set δ : ℝ := Op.gardingγ / (Op.gardingγ + C) with hδdef
    have hδ : 0 < δ := div_pos hγ hC
    have himg : (fun lam => Op.gardingγ / (Op.gardingγ + lam))
          '' (Op.sigmaSet Ω ∩ Set.Iic C)
        ⊆ {μ : ℝ | Module.End.HasEigenvalue (Op.opK Ω).toLinearMap μ ∧ δ ≤ ‖μ‖} := by
      rintro _ ⟨lam, ⟨hmem, hle⟩, rfl⟩
      obtain ⟨hne, heig⟩ := hmem
      have hpos := hposmem lam ⟨hne, heig⟩
      rw [Set.mem_Iic] at hle
      refine ⟨heig, ?_⟩
      have hμpos : 0 < Op.gardingγ / (Op.gardingγ + lam) :=
        Op.opK_eigenvalue_pos Ω heig (div_ne_zero hγ.ne' hne)
      rw [Real.norm_eq_abs, abs_of_pos hμpos, hδdef]
      gcongr
    have hfin : ((fun lam => Op.gardingγ / (Op.gardingγ + lam))
        '' (Op.sigmaSet Ω ∩ Set.Iic C)).Finite :=
      (hK.finite_setOf_hasEigenvalue_norm_ge hδ).subset himg
    refine Set.Finite.of_finite_image hfin ?_
    rintro lam1 hlam1 lam2 hlam2 heq
    have hpos1 := hposmem lam1 hlam1.1
    have hpos2 := hposmem lam2 hlam2.1
    rw [div_eq_div_iff hpos1.ne' hpos2.ne'] at heq
    have h2 := mul_left_cancel₀ hγ.ne' heq
    linarith

/-- The exceptional set `Σ` is countable: finite on each bounded slice `Σ ∩ (-∞, n]`. -/
theorem sigmaSet_countable (hK : IsCompactOperator (Op.opK Ω)) :
    (Op.sigmaSet Ω).Countable := by
  have hsub : Op.sigmaSet Ω ⊆ ⋃ n : ℕ, (Op.sigmaSet Ω ∩ Set.Iic (n : ℝ)) := by
    intro lam hlam
    obtain ⟨n, hn⟩ := exists_nat_ge lam
    exact Set.mem_iUnion.mpr ⟨n, hlam, hn⟩
  exact Set.Countable.mono hsub
    (Set.countable_iUnion (fun n => (Op.sigmaSet_inter_Iic_finite Ω hK n).countable))

/-- The zero `L²` right-hand side contributes a vanishing integral. -/
private lemma integral_zero_rhs (v : H01 Ω) :
    (∫ x in Ω, ((0 : L2D Ω) x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) = 0 := by
  have h1 : (∫ x in Ω, ((0 : L2D Ω) x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      = ∫ _x in Ω, (0 : ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with a ha
    rw [ha]
    simp
  rw [h1, integral_zero]

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
  refine ⟨Op.sigmaSet Ω, Op.sigmaSet_countable Ω hK,
    fun C => Op.sigmaSet_inter_Iic_finite Ω hK C, fun lam => ?_⟩
  constructor
  · intro hlam f
    have h1 := Op.solvable_of_notMem_sigmaSet Ω hK hlam (l2Functional Ω f)
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h1
    rw [l2Functional_eq_integral, zerothForm_apply]
  · intro hall
    by_contra hmem
    apply Op.not_unique_of_mem_sigmaSet Ω hmem
    have h0 := hall 0
    refine (existsUnique_congr (fun u => forall_congr' (fun v => ?_))).mp h0
    rw [integral_zero_rhs Ω v, add_zero, zerothForm_apply]

/-- **Boundedness of the resolvent.** For `λ ∉ Σ` there is a
constant `C > 0` such that every weak solution of `Lu = λu + f` with `f ∈ L²(Ω)`
satisfies `‖u‖_{L²} ≤ C ‖f‖_{L²}`. The constant is the operator norm of the
continuous inverse of the `λ`-shifted Riesz operator. -/
theorem resolvent_bound (hK : IsCompactOperator (Op.opK Ω)) {lam : ℝ}
    (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : L2D Ω, ∀ u : H01 Ω,
      (∀ v : H01 Ω, Op.fullBilin Ω u v
        = lam * ⟪(u : H1amb Ω) 0, ((v : H1amb Ω) 0)⟫
          + ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖(u : H1amb Ω) 0‖ ≤ C * ‖f‖ := by
  have hbij := Op.opAlam_bijective_of_notMem Ω hK hlam
  have hunit : IsUnit (Op.opAlam Ω lam) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  obtain ⟨w, hw⟩ := hunit
  set B : H01 Ω →L[ℝ] H01 Ω := ↑w⁻¹ with hBdef
  have hBA : ∀ y : H01 Ω, B (Op.opAlam Ω lam y) = y := by
    intro y
    have h1 : B * Op.opAlam Ω lam = 1 := by
      rw [hBdef, ← hw]
      exact w.inv_mul
    calc B (Op.opAlam Ω lam y) = (B * Op.opAlam Ω lam) y :=
        (mul_apply_eq_comp _ _ _).symm
      _ = (1 : H01 Ω →L[ℝ] H01 Ω) y := by rw [h1]
      _ = y := rfl
  refine ⟨‖B‖ + 1, by positivity, ?_⟩
  intro f u hu
  have hu' : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = lam * zerothForm Ω u v + l2Functional Ω f v := by
    intro v
    rw [zerothForm_apply, l2Functional_eq_integral]
    exact hu v
  have hAu : Op.opAlam Ω lam u
      = (InnerProductSpace.toDual ℝ (H01 Ω)).symm (l2Functional Ω f) :=
    (Op.opAlam_solves_iff Ω lam (l2Functional Ω f) u).mp hu'
  have hub : ‖u‖ ≤ ‖B‖ * ‖f‖ := by
    calc ‖u‖ = ‖B (Op.opAlam Ω lam u)‖ := by rw [hBA u]
      _ ≤ ‖B‖ * ‖Op.opAlam Ω lam u‖ := B.le_opNorm _
      _ = ‖B‖ * ‖(InnerProductSpace.toDual ℝ (H01 Ω)).symm (l2Functional Ω f)‖ := by
          rw [hAu]
      _ = ‖B‖ * ‖l2Functional Ω f‖ := by
          rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖B‖ * ‖f‖ :=
          mul_le_mul_of_nonneg_left (norm_l2Functional_le Ω f) (norm_nonneg B)
  calc ‖(u : H1amb Ω) 0‖ ≤ ‖u‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖B‖ * ‖f‖ := hub
    _ ≤ (‖B‖ + 1) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (by linarith [norm_nonneg B]) (norm_nonneg f)

end FullEllipticOp

end EllipticPdes.Sobolev
