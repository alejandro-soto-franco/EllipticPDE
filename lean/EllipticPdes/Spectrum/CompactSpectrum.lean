/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.CompactOperator
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Spectrum of a compact operator

Evans Appendix D.5, Theorem 6: the spectrum of a compact operator `K` on a real Hilbert space.
`0 ∈ σ(K)` when the space is infinite-dimensional; away from zero the spectrum consists of
eigenvalues (mathlib's Fredholm alternative); and the eigenvalues cannot accumulate away from
zero: for every `δ > 0` only finitely many eigenvalues have `|μ| ≥ δ`, so `σ(K) \ {0}` is
countable. The accumulation argument is the classical eigenvector chain: distinct eigenvalues
give a strictly increasing chain of spans `Eₙ`, Hilbert geometry provides unit vectors
`uₙ ∈ Eₙ₊₁ ∩ Eₙᗮ`, and `(μₙ - K)Eₙ₊₁ ⊆ Eₙ` forces `‖K(uₙ/μₙ) - K(uₘ/μₘ)‖ ≥ 1` for `m < n`,
contradicting the compactness of `K` on the bounded sequence `uₙ/μₙ`.
-/

@[expose] public section

open InnerProductSpace
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

end EllipticPdes.Sobolev
