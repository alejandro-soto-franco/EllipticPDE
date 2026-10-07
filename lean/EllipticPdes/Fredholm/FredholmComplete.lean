/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Fredholm.Fredholm
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Complete Fredholm theory

Evans §6.2.3, Theorem 4.

`Fredholm.lean` reduces the weak problem `Lu = f` to the compact-operator equation
`(1 - opK)u = h` through the factorisation `opA = opE ∘ (1 - opK)` and derives the
dichotomy. This module develops the Riesz theory of `1 - K` for a compact operator `K` on a
Hilbert space over `ℝ` or `ℂ` (`IsCompactOperator.fredholm_alternative`: finite-dimensional
kernel, closed range, `range (1 - K) = (ker (1 - K†))ᗮ`, injective iff surjective, and
`dim ker (1 - K) = dim ker (1 - K†)`, with Schauder's theorem `IsCompactOperator.adjoint`), and
instantiates it at `opK`: the space

  `N = {u ∈ H₀¹(Ω) : B[u, v] = 0 for all v}`

of weak solutions of the homogeneous problem is the eigenspace of `opK` at `1`, the adjoint
problem is the transpose form `B(·, v)`, and the solvability criterion `Lu = f` solvable
`↔ f ⊥ N*` holds with `dim N = dim N*`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

/-! ### Riesz theory for `1 - K` with `K` compact on a Hilbert space -/

section RieszTheory

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The kernel of `1 - K` is the eigenspace of `K` at the eigenvalue `1`. -/
lemma ContinuousLinearMap.ker_one_sub_eq_eigenspace (K : E →L[𝕜] E) :
    LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap = Module.End.eigenspace K.toLinearMap 1 := by
  ext u
  simp only [LinearMap.mem_ker, Module.End.mem_eigenspace_iff, one_smul,
    ContinuousLinearMap.coe_coe, sub_apply, one_apply_eq_self]
  rw [sub_eq_zero, eq_comm]

/-- **Finite-dimensionality of `ker(1 - K)`** for a compact operator `K` (Riesz theory): the
kernel is the eigenspace of `K` at the nonzero eigenvalue `1`. -/
theorem IsCompactOperator.finiteDimensional_ker_one_sub [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap) := by
  rw [ContinuousLinearMap.ker_one_sub_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

/-- A bounded-below failure on a subspace yields unit vectors of the subspace with arbitrarily
small image. -/
lemma exists_unit_mem_norm_apply_lt {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {T : E →L[𝕜] F} {S : Submodule 𝕜 E} (h : ¬∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, c * ‖x‖ ≤ ‖T x‖)
    {ε : ℝ} (hε : 0 < ε) : ∃ x ∈ S, ‖x‖ = 1 ∧ ‖T x‖ < ε := by
  push Not at h
  obtain ⟨x, hx, hlt⟩ := h ε hε
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hlt
  refine ⟨(‖x‖⁻¹ : 𝕜) • x, S.smul_mem _ hx, norm_smul_inv_norm hx0, ?_⟩
  rw [map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm, inv_mul_lt_iff₀
    (norm_pos_iff.mpr hx0), mul_comm]
  exact hlt

/-- If `x n - K (x n) → 0` along a bounded sequence and `K` is compact, a subsequence of `x`
converges to a fixed point of `K`. -/
theorem IsCompactOperator.exists_tendsto_of_tendsto_sub_apply {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) {x : ℕ → E} (hx : ∀ n, ‖x n‖ ≤ 1)
    (h0 : Filter.Tendsto (fun n => x n - K (x n)) Filter.atTop (nhds 0)) :
    ∃ (z : E) (φ : ℕ → ℕ), StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (nhds z) ∧
      K z = z := by
  have hmem : ∀ n, K (x n) ∈ closure (K.toLinearMap '' Metric.closedBall 0 1) := fun n =>
    subset_closure ⟨x n, by simpa using hx n, rfl⟩
  obtain ⟨w, -, φ, hφ, hw⟩ := (hK.isCompact_closure_image_closedBall 1).tendsto_subseq hmem
  have hxw : Filter.Tendsto (x ∘ φ) Filter.atTop (nhds w) := by
    simpa [Function.comp_def] using ((h0.comp hφ.tendsto_atTop).add hw :)
  exact ⟨w, φ, hφ, hxw, tendsto_nhds_unique ((K.continuous.tendsto w).comp hxw) hw⟩

/-- `1 - K` is **bounded below on the orthogonal complement of its kernel**: the main step of
the Riesz closed-range theorem, by the standard compactness contradiction. Normalised
`xₙ ∈ (ker(1-K))ᗮ` with `(1-K)xₙ → 0` have a subsequence converging to a unit vector of
`ker(1-K) ∩ (ker(1-K))ᗮ`. -/
theorem IsCompactOperator.exists_pos_bound_on_orthogonal_ker {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap)ᗮ,
      c * ‖x‖ ≤ ‖(1 - K : E →L[𝕜] E) x‖ := by
  by_contra hcon
  choose y hymem hy1 hylt using fun n : ℕ => exists_unit_mem_norm_apply_lt hcon
    (ε := 1 / (n + 1)) (by positivity)
  have h0 : Filter.Tendsto (fun n => y n - K (y n)) Filter.atTop (nhds 0) := by
    simpa using squeeze_zero_norm (fun n => (hylt n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨z, φ, hφ, hlim, hz⟩ := hK.exists_tendsto_of_tendsto_sub_apply (fun n => (hy1 n).le) h0
  have hz1 : ‖z‖ = 1 := tendsto_nhds_unique hlim.norm
    (tendsto_const_nhds.congr fun n => (hy1 (φ n)).symm)
  have hzN : z ∈ LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap := by simp [hz]
  have hzNp : z ∈ (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap)ᗮ :=
    Submodule.isClosed_orthogonal _ |>.mem_of_tendsto hlim (.of_forall fun n => hymem (φ n))
  have := (Submodule.orthogonal_disjoint _).le_bot (Submodule.mem_inf.mpr ⟨hzN, hzNp⟩)
  simp_all

/-- **Closed range from a lower bound.** If `T` is bounded below on the orthogonal complement
of its kernel then its range is closed: the range is the image of that complement, on which
`T` is antilipschitz. -/
theorem ContinuousLinearMap.isClosed_range_of_le_norm_on_orthogonal_ker [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) {c : ℝ} (hc : 0 < c)
    (hbd : ∀ x ∈ (LinearMap.ker T.toLinearMap)ᗮ, c * ‖x‖ ≤ ‖T x‖) : IsClosed (Set.range T) := by
  set N := LinearMap.ker T.toLinearMap
  have : CompleteSpace N := T.isClosed_ker.completeSpace_coe
  have hanti : AntilipschitzWith (c⁻¹).toNNReal (T.comp Nᗮ.subtypeL) :=
    (T.comp Nᗮ.subtypeL).antilipschitz_of_bound fun x => by
      rw [Real.coe_toNNReal _ (by positivity), inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
      exact hbd x x.2
  convert hanti.isClosed_range (T.comp Nᗮ.subtypeL).uniformContinuous using 1
  ext w
  refine ⟨?_, fun ⟨m, hm⟩ => ⟨(m : E), hm⟩⟩
  rintro ⟨x, rfl⟩
  obtain ⟨n, hn, m, hm, rfl⟩ := N.exists_add_mem_mem_orthogonal x
  have hn0 : T n = 0 := LinearMap.mem_ker.mp hn
  exact ⟨⟨m, hm⟩, by simp [hn0]⟩

/-- **Closed range (Riesz theory).** For a compact operator `K` on a Hilbert space the range of
`1 - K` is closed. -/
theorem IsCompactOperator.isClosed_range_one_sub [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) : IsClosed (Set.range (1 - K : E →L[𝕜] E)) := by
  obtain ⟨c, hc, hbd⟩ := hK.exists_pos_bound_on_orthogonal_ker
  exact (1 - K).isClosed_range_of_le_norm_on_orthogonal_ker hc hbd

/-- A closed-range operator on a Hilbert space has range exactly the orthogonal complement of
the kernel of its adjoint: `range A = (ker A†)ᗮ`. -/
lemma ContinuousLinearMap.range_eq_orthogonal_ker_adjoint [CompleteSpace E] (A : E →L[𝕜] E)
    (hA : IsClosed (Set.range A)) :
    LinearMap.range A.toLinearMap
      = (LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap)ᗮ := by
  rw [← ContinuousLinearMap.orthogonal_range A, Submodule.orthogonal_orthogonal_eq_closure]
  exact (IsClosed.submodule_topologicalClosure_eq (by rw [LinearMap.coe_range]; exact hA)).symm

/-- `A u` lies in `ker A†` only if `A u = 0`, since `⟪A u, A u⟫ = ⟪A† A u, u⟫`. -/
lemma ContinuousLinearMap.apply_eq_zero_of_apply_mem_ker_adjoint [CompleteSpace E]
    (A : E →L[𝕜] E) {u : E} (h : A u ∈ LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap) :
    A u = 0 := by
  refine (inner_self_eq_zero (𝕜 := 𝕜)).mp ?_
  have h0 : ContinuousLinearMap.adjoint A (A u) = 0 := h
  rw [← ContinuousLinearMap.adjoint_inner_left, h0, inner_zero_left]

/-- For `T = K†`: `‖K† z‖² ≤ ‖z‖ ‖K (K† z)‖`. -/
lemma ContinuousLinearMap.norm_adjoint_apply_sq_le [CompleteSpace E] (K : E →L[𝕜] E) (z : E) :
    ‖ContinuousLinearMap.adjoint K z‖ ^ 2 ≤ ‖z‖ * ‖K (ContinuousLinearMap.adjoint K z)‖ := by
  have h : inner 𝕜 (ContinuousLinearMap.adjoint K z) (ContinuousLinearMap.adjoint K z)
      = inner 𝕜 z (K (ContinuousLinearMap.adjoint K z)) := ContinuousLinearMap.adjoint_inner_left ..
  rw [inner_self_eq_norm_sq_to_K] at h
  calc ‖ContinuousLinearMap.adjoint K z‖ ^ 2
      = ‖inner 𝕜 z (K (ContinuousLinearMap.adjoint K z))‖ := by rw [← h]; simp
    _ ≤ _ := norm_inner_le_norm _ _

/-- A real-metric lemma: a map `A` that is controlled in square by a totally bounded map `S`
(`dist (A x) (A y) ^ 2 ≤ C * dist (S x) (S y)` on `B`) is totally bounded on `B`. -/
theorem TotallyBounded.image_of_sq_dist_le {α β γ : Type*} [PseudoMetricSpace β]
    [PseudoMetricSpace γ] {A : α → β} {S : α → γ} {B : Set α} {C : ℝ}
    (hS : TotallyBounded (S '' B))
    (h : ∀ x ∈ B, ∀ y ∈ B, dist (A x) (A y) ^ 2 ≤ C * dist (S x) (S y)) :
    TotallyBounded (A '' B) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ := ε ^ 2 / (|C| + 1) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨t, ht, htfin, hcov⟩ := Metric.finite_approx_of_totallyBounded hS δ hδpos
  obtain ⟨t', ht'B, ht'fin, hcov⟩ := (Set.exists_subset_image_finite_and
    (p := fun t => S '' B ⊆ ⋃ y ∈ t, Metric.ball y δ)).mp ⟨t, ht, htfin, hcov⟩
  refine ⟨A '' t', ht'fin.image _, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := Set.mem_iUnion₂.mp (hcov ⟨y, hy, rfl⟩)
  refine Set.mem_iUnion₂.mpr ⟨A x, ⟨x, hx, rfl⟩, ?_⟩
  rw [Metric.mem_ball] at hxy ⊢
  refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
  calc dist (A y) (A x) ^ 2 ≤ C * dist (S y) (S x) := h y hy x (ht'B hx)
    _ ≤ |C| * δ := (mul_le_mul_of_nonneg_right (le_abs_self C) dist_nonneg).trans
        (mul_le_mul_of_nonneg_left hxy.le (abs_nonneg C))
    _ < ε ^ 2 := by rw [hδ]; field_simp; linarith [abs_nonneg C]

/-- **Schauder's theorem** on a Hilbert space: the adjoint of a compact operator is compact.
The proof is `‖K†x - K†y‖² ≤ ‖x - y‖ ‖KK†x - KK†y‖`, so total boundedness of the image of the unit
ball under `KK†` gives total boundedness of its image under `K†`. -/
theorem IsCompactOperator.adjoint [CompleteSpace E] {K : E →L[𝕜] E} (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) := by
  set Kd := ContinuousLinearMap.adjoint K
  have hS : TotallyBounded ((K.comp Kd) '' Metric.ball 0 1) :=
    ((hK.comp_clm Kd).isCompact_closure_image_ball 1).totallyBounded.subset subset_closure
  have key : TotallyBounded (Kd '' Metric.ball 0 1) := hS.image_of_sq_dist_le (C := 2)
    fun x hx y hy => by
      have hxy : ‖x - y‖ ≤ 2 := (norm_sub_le x y).trans (by
        linarith [mem_ball_zero_iff.mp hx, mem_ball_zero_iff.mp hy])
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub]
      exact (K.norm_adjoint_apply_sq_le (x - y)).trans
        (mul_le_mul_of_nonneg_right hxy (norm_nonneg _))
  exact (isCompactOperator_iff_isCompact_closure_image_ball Kd.toLinearMap one_pos).mpr
    (key.closure.isCompact_of_isComplete isClosed_closure.isComplete)


/-- The adjoint of `1 - K` is `1 - K†`. -/
lemma ContinuousLinearMap.adjoint_one_sub [CompleteSpace E] (K : E →L[𝕜] E) :
    ContinuousLinearMap.adjoint (1 - K : E →L[𝕜] E) = 1 - ContinuousLinearMap.adjoint K := by
  rw [map_sub, ContinuousLinearMap.adjoint_one]

/-- If `1 - K` is injective for a compact operator `K`, it is bijective (Fredholm alternative at
the eigenvalue `1`). -/
theorem IsCompactOperator.bijective_one_sub_of_ker_eq_bot [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) (h : LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap = ⊥) :
    Function.Bijective (1 - K : E →L[𝕜] E) := by
  rcases hK.hasEigenvalue_or_mem_resolventSet (μ := (1 : 𝕜)) one_ne_zero with he | hr
  · exact absurd ((ContinuousLinearMap.ker_one_sub_eq_eigenspace K).symm.trans h)
      (show Module.End.eigenspace K.toLinearMap 1 ≠ ⊥ from he)
  · rw [spectrum.mem_resolventSet_iff, map_one] at hr
    exact ContinuousLinearMap.isUnit_iff_bijective.mp hr

/-- **Index inequality, surjectivity form.** For a compact operator `K`, every injective linear
map `Λ : ker(1 - K) → ker(1 - K†)` is surjective. Otherwise `1 - (K + Φ)`, with the finite-rank
perturbation `Φ = ι ∘ Λ ∘ P`, would be injective but miss a point of `ker(1 - K†)` (Brezis
Theorem 6.6 adapted to the Hilbert setting). -/
theorem IsCompactOperator.surjective_of_injective_ker_one_sub [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K)
    (Λ : LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap →ₗ[𝕜]
      LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap)
    (hΛ : Function.Injective Λ) : Function.Surjective Λ := by
  have := hK.finiteDimensional_ker_one_sub
  have := hK.adjoint.finiteDimensional_ker_one_sub
  revert Λ
  set N := LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap
  set N' := LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap
  intro Λ hΛ
  set Φ : E →L[𝕜] E := N'.subtypeL.comp
    ((LinearMap.toContinuousLinearMap Λ).comp N.orthogonalProjectionOnto)
  have hΦc : IsCompactOperator Φ :=
    (isCompactOperator_of_locallyCompactSpace_dom
      ((LinearMap.toContinuousLinearMap Λ).comp N.orthogonalProjectionOnto)).clm_comp N'.subtypeL
  have hΦ : ∀ u, (1 - (K + Φ) : E →L[𝕜] E) u = (1 - K : E →L[𝕜] E) u - Φ u := fun u => by
    simp [sub_sub]
  have hΦu : ∀ u, Φ u = (Λ (N.orthogonalProjectionOnto u) : E) := fun _ => rfl
  have hkey : ∀ u, (1 - K : E →L[𝕜] E) u ∈ N' → (1 - K : E →L[𝕜] E) u = 0 := fun u hu =>
    (1 - K).apply_eq_zero_of_apply_mem_ker_adjoint (by rwa [ContinuousLinearMap.adjoint_one_sub])
  have hinj : LinearMap.ker (1 - (K + Φ) : E →L[𝕜] E).toLinearMap = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
    have h1 : (1 - K : E →L[𝕜] E) u = Φ u := by
      have := LinearMap.mem_ker.mp hu
      rwa [ContinuousLinearMap.coe_coe, hΦ, sub_eq_zero] at this
    have h0 : (1 - K : E →L[𝕜] E) u = 0 := hkey u (h1 ▸ (Λ (N.orthogonalProjectionOnto u)).2)
    have hP : N.orthogonalProjectionOnto u = 0 := hΛ (by
      rw [map_zero]
      exact Subtype.ext ((hΦu u).symm.trans (h1.symm.trans h0)))
    exact (Submodule.mem_bot 𝕜).mp ((Submodule.orthogonal_disjoint N).le_bot
      ⟨LinearMap.mem_ker.mpr h0, Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hP⟩)
  intro y
  obtain ⟨u, hu⟩ := (hK.add hΦc).bijective_one_sub_of_ker_eq_bot hinj |>.2 (y : E)
  have h1 : (1 - K : E →L[𝕜] E) u = (y : E) + Φ u := by
    rw [hΦ] at hu
    rw [← hu]
    abel
  have h0 := hkey u (h1 ▸ N'.add_mem y.2 (Λ (N.orthogonalProjectionOnto u)).2)
  rw [h0, hΦu] at h1
  exact ⟨-(N.orthogonalProjectionOnto u), Subtype.ext (by
    simpa using neg_eq_of_add_eq_zero_left h1.symm)⟩

/-- **One inequality of the index theorem**: `dim ker(1 - K†) ≤ dim ker(1 - K)` for a compact
operator `K`. -/
theorem IsCompactOperator.finrank_ker_one_sub_adjoint_le [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    Module.finrank 𝕜 (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap)
      ≤ Module.finrank 𝕜 (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap) := by
  set N := LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap
  set N' := LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap
  have := hK.finiteDimensional_ker_one_sub
  have := hK.adjoint.finiteDimensional_ker_one_sub
  by_contra hcon
  obtain ⟨Λ, hΛ⟩ := Module.Free.exists_linearMap_injective_of_rank_lt (R := 𝕜)
    (M := N) (N := N') (by
      rw [← Module.finrank_eq_rank 𝕜 N, ← Module.finrank_eq_rank 𝕜 N']
      exact_mod_cast not_le.mp hcon)
  have := LinearMap.finrank_range_le Λ
  rw [LinearMap.range_eq_top.mpr (hK.surjective_of_injective_ker_one_sub Λ hΛ), finrank_top]
    at this
  exact hcon this

/-- **`dim ker(1 - K) = dim ker(1 - K†)`** for a compact operator on a Hilbert space (the
abstract form of Evans §6.2.3, Theorem 4(ii)): the index of `1 - K` is zero. -/
theorem IsCompactOperator.finrank_ker_one_sub_adjoint_eq [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    Module.finrank 𝕜 (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap)
      = Module.finrank 𝕜 (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap) := by
  refine le_antisymm hK.finrank_ker_one_sub_adjoint_le ?_
  have h := hK.adjoint.finrank_ker_one_sub_adjoint_le
  rwa [ContinuousLinearMap.adjoint_adjoint] at h

/-- The adjoint of (the underlying map of) a continuous linear equivalence is bijective: it is
the star of a unit. -/
lemma ContinuousLinearMap.bijective_adjoint_of_equiv [CompleteSpace E] (e : E ≃L[𝕜] E) :
    Function.Bijective (ContinuousLinearMap.adjoint (e : E →L[𝕜] E)) := by
  have h := (ContinuousLinearMap.isUnit_iff_bijective.2
    (show Function.Bijective (e : E →L[𝕜] E) from e.bijective)).star
  rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.isUnit_iff_bijective] at h

/-- If `A = e ∘ (1 - K)` for an equivalence `e`, then `ker A†` has the same dimension as
`ker (1 - K†)`: `ker A† = (e†)⁻¹ ker (1 - K†)`. -/
lemma ContinuousLinearMap.finrank_ker_adjoint_of_eq_comp_equiv [CompleteSpace E]
    {K A : E →L[𝕜] E} (e : E ≃L[𝕜] E) (hA : A = (e : E →L[𝕜] E).comp (1 - K)) :
    Module.finrank 𝕜 (LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap)
      = Module.finrank 𝕜
          (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap) := by
  let T : E ≃ₗ[𝕜] E := LinearEquiv.ofBijective
    (ContinuousLinearMap.adjoint (e : E →L[𝕜] E)).toLinearMap
    (ContinuousLinearMap.bijective_adjoint_of_equiv e)
  have hker : LinearMap.ker (ContinuousLinearMap.adjoint A).toLinearMap
      = (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap).map
        (T.symm : E →ₗ[𝕜] E) := by
    rw [← Submodule.comap_equiv_eq_map_symm]
    ext x
    simp [LinearMap.mem_ker, hA, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_one, T]
  rw [hker, LinearEquiv.finrank_map_eq]

/-- **Fredholm alternative** (Evans Appendix D Theorem 5, Guo Theorem VII.4.4) for a compact
operator `K` on a Hilbert space: the kernel of `1 - K` is finite dimensional, the range of
`1 - K` is closed and is the orthogonal complement of the kernel of `1 - K†`, `1 - K` is
injective exactly when it is surjective, and the kernels of `1 - K` and `1 - K†` have the same
dimension. -/
theorem IsCompactOperator.fredholm_alternative [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    FiniteDimensional 𝕜 (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap) ∧
    IsClosed (Set.range (1 - K : E →L[𝕜] E)) ∧
    LinearMap.range (1 - K : E →L[𝕜] E).toLinearMap
      = (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap)ᗮ ∧
    (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap = ⊥ ↔
      LinearMap.range (1 - K : E →L[𝕜] E).toLinearMap = ⊤) ∧
    Module.finrank 𝕜
        (LinearMap.ker (1 - ContinuousLinearMap.adjoint K : E →L[𝕜] E).toLinearMap)
      = Module.finrank 𝕜 (LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap) := by
  have hrange := (1 - K).range_eq_orthogonal_ker_adjoint hK.isClosed_range_one_sub
  rw [ContinuousLinearMap.adjoint_one_sub] at hrange
  have hrank := hK.finrank_ker_one_sub_adjoint_eq
  refine ⟨hK.finiteDimensional_ker_one_sub, hK.isClosed_range_one_sub, hrange,
    ⟨fun hker => LinearMap.range_eq_top.mpr (hK.bijective_one_sub_of_ker_eq_bot hker).2,
      fun hran => ?_⟩, hrank⟩
  have := hK.finiteDimensional_ker_one_sub
  rw [hran, eq_comm, Submodule.orthogonal_eq_top_iff] at hrange
  rw [hrange, finrank_bot] at hrank
  exact Submodule.finrank_eq_zero.mp hrank.symm

/-- For a compact operator `K` and a nonzero scalar `c` such that `c⁻¹` is not an eigenvalue of
`K`, the operator `1 - c K` is bijective. -/
theorem IsCompactOperator.bijective_one_sub_smul [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) {c : 𝕜} (hc : c ≠ 0)
    (h : ¬ Module.End.HasEigenvalue (K : Module.End 𝕜 E) c⁻¹) :
    Function.Bijective (1 - c • K : E →L[𝕜] E) := by
  rcases hK.hasEigenvalue_or_mem_resolventSet (μ := c⁻¹) (inv_ne_zero hc) with he | hr
  · exact absurd he h
  · have hunit := spectrum.mem_resolventSet_iff.mp hr
    have hfac : (1 - c • K : E →L[𝕜] E)
        = algebraMap 𝕜 (E →L[𝕜] E) c * (algebraMap 𝕜 (E →L[𝕜] E) c⁻¹ - K) := by
      rw [mul_sub, ← map_mul, mul_inv_cancel₀ hc, map_one, ← Algebra.smul_def]
    exact ContinuousLinearMap.isUnit_iff_bijective.mp (hfac ▸
      ((isUnit_iff_ne_zero.mpr hc).map (algebraMap 𝕜 (E →L[𝕜] E))).mul hunit)

/-- **Fredholm dichotomy** (Evans Appendix D Theorem 5, the remark following it; Guo Theorem
VII.4.4): either `(1 - K) u = h` has exactly one solution for every `h`, or the homogeneous
equation has a nonzero solution. -/
theorem IsCompactOperator.fredholm_dichotomy [CompleteSpace E] {K : E →L[𝕜] E}
    (hK : IsCompactOperator K) :
    (∀ h : E, ∃! u : E, (1 - K : E →L[𝕜] E) u = h)
      ∨ ∃ u : E, u ≠ 0 ∧ (1 - K : E →L[𝕜] E) u = 0 := by
  by_cases hker : LinearMap.ker (1 - K : E →L[𝕜] E).toLinearMap = ⊥
  · exact .inl (hK.bijective_one_sub_of_ker_eq_bot hker).existsUnique
  · obtain ⟨u, hu, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    exact .inr ⟨u, hne, hu⟩

end RieszTheory

namespace EllipticPdes.Sobolev

section RieszTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E}

/-- **Fredholm alternative** (Evans Appendix D Theorem 5, Guo Theorem VII.4.4) for a compact
operator `K` on a real Hilbert space: the kernel of `1 - K` is finite dimensional, the range of
`1 - K` is closed and is the orthogonal complement of the kernel of `1 - K†`, `1 - K` is
injective exactly when it is surjective, and the kernels of `1 - K` and `1 - K†` have the same
dimension. -/
theorem fredholm_alternative_compact (hK : IsCompactOperator K) :
    FiniteDimensional ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) ∧
    IsClosed (Set.range (1 - K : E →L[ℝ] E)) ∧
    LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap
      = (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)ᗮ ∧
    (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap = ⊥ ↔
      LinearMap.range ((1 - K : E →L[ℝ] E)).toLinearMap = ⊤) ∧
    Module.finrank ℝ
        (LinearMap.ker ((1 - ContinuousLinearMap.adjoint K : E →L[ℝ] E)).toLinearMap)
      = Module.finrank ℝ (LinearMap.ker ((1 - K : E →L[ℝ] E)).toLinearMap) :=
  hK.fredholm_alternative

/-- **Fredholm dichotomy** (Evans Appendix D Theorem 5, the remark following it; Guo Theorem
VII.4.4): either `(1 - K) u = h` has exactly one solution for every `h`, or the homogeneous
equation has a nonzero solution. -/
theorem fredholm_dichotomy_compact (hK : IsCompactOperator K) :
    (∀ h : E, ∃! u : E, (1 - K : E →L[ℝ] E) u = h)
      ∨ ∃ u : E, u ≠ 0 ∧ (1 - K : E →L[ℝ] E) u = 0 :=
  hK.fredholm_dichotomy

end RieszTheory

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The space `N` of weak solutions of the homogeneous problem `Lu = 0`: the kernel of
the Riesz representative `opA` of the full divergence form. -/
def solSpace : Submodule ℝ (H01 Ω) := LinearMap.ker (Op.opA Ω).toLinearMap

/-- Membership in `solSpace` is exactly being a weak solution of the homogeneous
problem: `B[u, v] = 0` against every `v ∈ H₀¹(Ω)`. The proofs below reach `solSpace`
through `solSpace_eq_eigenspace` instead. -/
lemma mem_solSpace_iff (u : H01 Ω) :
    u ∈ Op.solSpace Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0 := by
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω u v, hu, inner_zero_left]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opA Ω u v, hu v, inner_zero_left]

/-- The homogeneous solution space is the eigenspace of the compact part `opK` at the
eigenvalue `1`: since `opA = opE ∘ (1 - opK)` with `opE` an equivalence,
`opA u = 0 ↔ opK u = u`. -/
lemma solSpace_eq_eigenspace :
    Op.solSpace Ω = Module.End.eigenspace (Op.opK Ω).toLinearMap 1 := by
  ext u
  rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Module.End.mem_eigenspace_iff, one_smul]
  have hfac : Op.opA Ω u = (Op.opE Ω) ((1 - Op.opK Ω) u) := by
    rw [Op.opA_factor Ω]; rfl
  constructor
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      apply (Op.opE Ω).injective
      rw [← hfac, hu, map_zero]
    rw [_root_.sub_apply, one_apply_eq_self, sub_eq_zero] at h0
    exact h0.symm
  · intro hu
    have h0 : (1 - Op.opK Ω) u = 0 := by
      rw [_root_.sub_apply, one_apply_eq_self,
        show Op.opK Ω u = u from hu, sub_self]
    rw [hfac, h0, map_zero]

/-- **Finite-dimensionality of the homogeneous solution space** (the finite-dimensionality
half of Evans §6.2.3, Theorem 4(ii)).
Under the Rellich-Kondrachov input (`opK` compact), the space of weak solutions of the
homogeneous problem `Lu = 0` is finite-dimensional: it is the eigenspace of the compact
operator `opK` at the nonzero eigenvalue `1`, and Riesz theory makes such eigenspaces
finite-dimensional. -/
theorem finiteDimensional_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    FiniteDimensional ℝ (Op.solSpace Ω) := by
  rw [solSpace_eq_eigenspace]
  exact ContinuousLinearMap.finite_dimensional_eigenspace hK 1 one_ne_zero

/-- **Closed range of the elliptic operator** (towards Evans §6.2.3, Theorem
4(ii)-(iii)). Under
the Rellich-Kondrachov input the range of `opA` (the set of Riesz representatives of
solvable right-hand sides) is closed: `opA = opE ∘ (1 - opK)` with `opE` a
homeomorphism, and `1 - opK` has closed range by Riesz theory. This is the geometric
input for the solvability criterion `Lu = f solvable ↔ f ⊥ N*`. -/
theorem isClosed_range_opA (hK : IsCompactOperator (Op.opK Ω)) :
    IsClosed (Set.range (Op.opA Ω)) := by
  have h1 : IsClosed (Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω)) :=
    hK.isClosed_range_one_sub
  have h2 : Set.range (Op.opA Ω)
      = (Op.opE Ω) '' Set.range (1 - Op.opK Ω : H01 Ω →L[ℝ] H01 Ω) := by
    rw [Op.opA_factor Ω, ContinuousLinearMap.coe_comp, Set.range_comp]
    rfl
  rw [h2]
  exact (Op.opE Ω).toHomeomorph.isClosedMap _ h1

/-- The **adjoint solution space** `N*`: the kernel of the Hilbert adjoint of `opA`,
which is exactly the space of weak solutions of the **transpose problem**
`B[v, u] = 0` for all `v` (the adjoint bilinear form and adjoint problem defined ahead
of Evans §6.2.3, Theorem 4: the adjoint problem is the transpose form, with no
differentiability demanded of the coefficients). -/
def solSpaceStar : Submodule ℝ (H01 Ω) :=
  LinearMap.ker (ContinuousLinearMap.adjoint (Op.opA Ω)).toLinearMap

/-- Membership in `solSpaceStar` is exactly being a weak solution of the transpose
problem: `B[v, u] = 0` against every `v ∈ H₀¹(Ω)`, the transpose counterpart of
`mem_solSpace_iff`. -/
lemma mem_solSpaceStar_iff (u : H01 Ω) :
    u ∈ Op.solSpaceStar Ω ↔ ∀ v : H01 Ω, Op.fullBilin Ω v u = 0 := by
  rw [solSpaceStar, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω v u, ← ContinuousLinearMap.adjoint_inner_right, hu,
      inner_zero_right]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm,
      Op.inner_opA Ω v u]
    exact hu v

/-- **Solvability criterion** (Evans §6.2.3, Theorem 4(iii)). Under the
Rellich-Kondrachov input, the weak problem `Lu = f` is solvable exactly when `f`
annihilates the adjoint solution space: `∃u ∀v, B[u, v] = f(v)` iff `f(w) = 0` for
every weak solution `w` of the transpose problem `B[v, w] = 0`. The proof is closed
range (`isClosed_range_opA`) plus the Hilbert-space duality
`range A = (ker A†)ᗮ`. -/
theorem solvable_iff_orthogonal_solSpaceStar (hK : IsCompactOperator (Op.opK Ω))
    (f : H01 Ω →L[ℝ] ℝ) :
    (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ ∀ w ∈ Op.solSpaceStar Ω, f w = 0 := by
  set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hg
  have hgrep : ∀ v : H01 Ω, ⟪g, v⟫ = f v := fun v => InnerProductSpace.toDual_symm_apply
  have hiff : (∃ u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v)
      ↔ g ∈ LinearMap.range (Op.opA Ω).toLinearMap := by
    rw [LinearMap.mem_range]
    exact exists_congr fun u => (Op.opA_eq_toDual_symm_iff Ω f u).symm
  rw [hiff, ContinuousLinearMap.range_eq_orthogonal_ker_adjoint _
    (Op.isClosed_range_opA Ω hK),
    Submodule.mem_orthogonal]
  constructor
  · intro h w hw
    rw [← hgrep w, real_inner_comm]
    exact h w hw
  · intro h w hw
    rw [real_inner_comm, hgrep w]
    exact h w hw

/-- **`dim N = dim N*` for the elliptic problem** (Evans §6.2.3, Theorem 4(ii)). The space of
weak solutions of the homogeneous problem and the space of weak solutions of the transpose
problem have the same (finite) dimension. The factorisation `opA = opE ∘ (1 - opK)` maps
`solSpaceStar = ker(opA†)` onto `ker(1 - opK†)` along the bijection `(opE)†`, and the abstract
index theorem `finrank_ker_one_sub_adjoint_eq` applies. -/
theorem finrank_solSpaceStar_eq_finrank_solSpace (hK : IsCompactOperator (Op.opK Ω)) :
    Module.finrank ℝ (Op.solSpaceStar Ω) = Module.finrank ℝ (Op.solSpace Ω) := by
  rw [solSpaceStar, ContinuousLinearMap.finrank_ker_adjoint_of_eq_comp_equiv (Op.opE Ω)
    (Op.opA_factor Ω), hK.finrank_ker_one_sub_adjoint_eq,
    ContinuousLinearMap.ker_one_sub_eq_eigenspace, ← Op.solSpace_eq_eigenspace Ω]

/-- **Fredholm alternative for the elliptic Dirichlet problem** (Evans §6.2.3, Theorem 4).
Assume the operator `opK` is compact: the Rellich-Kondrachov input, that `H₀¹(Ω) ↪ L²(Ω)` is a
compact embedding. Then exactly one of two alternatives holds: either the homogeneous problem
`Lu = 0` has a nontrivial weak solution `u ≠ 0` (`∀ v, B[u, v] = 0`), or the inhomogeneous
problem `Lu = f` has a unique weak solution for every continuous functional `f`. -/
theorem fredholm_alternative (hK : IsCompactOperator (Op.opK Ω)) :
    (∃ u : H01 Ω, u ≠ 0 ∧ ∀ v : H01 Ω, Op.fullBilin Ω u v = 0)
      ∨ (∀ f : H01 Ω →L[ℝ] ℝ, ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) := by
  rcases fredholm_dichotomy_compact hK with h | ⟨u, hu0, hu⟩
  · right
    intro f
    refine (existsUnique_congr fun u => ?_).mp (h ((Op.opE Ω).symm
      ((InnerProductSpace.toDual ℝ (H01 Ω)).symm f)))
    rw [← Op.opA_eq_toDual_symm_iff Ω f u, (Op.opE Ω).eq_symm_apply, Op.opA_factor Ω]
    exact Iff.rfl
  · left
    refine ⟨u, hu0, (Op.mem_solSpace_iff Ω u).1 ?_⟩
    rw [solSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Op.opA_factor Ω,
      ContinuousLinearMap.comp_apply, hu, map_zero]

/-- **Fredholm corollary** (the usual working form, Evans §6.2.3): if the homogeneous problem
`Lu = 0` has only the trivial weak solution, then `Lu = f` has a unique weak solution for every
`f`. Uniqueness of the homogeneous problem rules out the eigenvalue alternative. -/
theorem fredholm_unique_imp_exists (hK : IsCompactOperator (Op.opK Ω))
    (huniq : ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = 0) → u = 0)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v := by
  rcases Op.fredholm_alternative Ω hK with ⟨u, hu_ne, hu_hom⟩ | hexists
  · exact absurd (huniq u hu_hom) hu_ne
  · exact hexists f

end FullEllipticOp

end EllipticPdes.Sobolev
