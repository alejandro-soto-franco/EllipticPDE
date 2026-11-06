/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.NormedDivForm.Basic
public import EllipticPdes.DivFormHaar
public import EllipticPdes.Form.DivFormGarding

/-!
# Weak theory of a divergence-form operator on a normed space

Every theorem of `DivFormHaar.lean`, the existence theorem of `DivFormExistence.lean` and the
Gårding inequality of `DivFormGarding.lean` has a twin here for a divergence-form operator on a
finite-dimensional real normed space `E` with an additive Haar measure `μ`, stated on
`W₀^{1,2}(Ω)`. Each is proved by transfer along `toEuclidean`: a functional or an `L²` datum is
pushed to the image, the inner-product theorem is applied to `Op.transfer`, and the conclusion is
pulled back along `transferEquiv`.

The transfer preserves the `L²` pairing exactly, since `toEuclidean.symm` is measure-preserving
from the pushforward back to `μ`. It does not preserve the `W₀^{1,2}` norm, so constants that
depend on it (the Gårding constants, the bound of the existence theorem) are stated as
existentials.

## Main declarations

* `EllipticPdes.NormedDivForm.FullEllipticOp.weak_solution_of_nonneg_zeroth_of_bounded`
* `EllipticPdes.NormedDivForm.FullEllipticOp.garding`
* `EllipticPdes.NormedDivForm.FullEllipticOp.fredholm_alternative_of_bounded_haar`
* `EllipticPdes.NormedDivForm.FullEllipticOp.solvable_iff_orthogonal_transpose_of_bounded_haar`
* `EllipticPdes.NormedDivForm.FullEllipticOp.sigmaSet`
* `EllipticPdes.NormedDivForm.FullEllipticOp.existence_three_of_bounded_haar`
* `EllipticPdes.NormedDivForm.FullEllipticOp.symmetric_spectral_of_bounded_haar`
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes

namespace NormedDivForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

local notation "𝔽" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝓛" => (toEuclidean (E := E))
local notation "𝓛'" => ContinuousLinearEquiv.symm (toEuclidean (E := E))

/-- The image of a measurable set under `toEuclidean` is measurable. -/
lemma measurableSet_image {Ω : Set E} (hΩ : MeasurableSet Ω) : MeasurableSet (𝓛 '' Ω) :=
  (toEuclidean (E := E)).toHomeomorph.toMeasurableEquiv.measurableSet_image.2 hΩ

omit [BorelSpace E] [MeasurableSpace E] in
/-- The image of a bounded set under `toEuclidean` is bounded. -/
lemma isBounded_image {Ω : Set E} (hΩ : Bornology.IsBounded Ω) :
    Bornology.IsBounded (𝓛 '' Ω) :=
  (toEuclidean (E := E) : E →L[ℝ] 𝔽).lipschitzWith.isBounded_image hΩ

namespace Transport

variable {A B L₁ L₂ : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup L₁] [InnerProductSpace ℝ L₁]
  [NormedAddCommGroup L₂] [InnerProductSpace ℝ L₂]
  (T : A ≃L[ℝ] B) {BA : A →L[ℝ] A →L[ℝ] ℝ} {BB : B →L[ℝ] B →L[ℝ] ℝ}

/-- The inverse of a continuous linear equivalence is bounded by a constant. -/
lemma exists_norm_le : ∃ K : ℝ, 0 < K ∧ ∀ u : A, ‖u‖ ≤ K * ‖T u‖ := by
  refine ⟨‖T.symm.toContinuousLinearMap‖ + 1, by positivity, fun u => ?_⟩
  have h := T.symm.toContinuousLinearMap.le_opNorm (T u)
  have h2 : ‖u‖ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T u‖ := by simpa using h
  exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

variable (hform : ∀ u v, BA u v = BB (T u) (T v))
include hform

lemma forwards (u : A) (g : B → ℝ) (hu : ∀ v, BA u v = g (T v)) : ∀ V, BB (T u) V = g V := by
  intro V
  have := hu (T.symm V)
  rw [hform] at this
  simpa using this

lemma backwards (u : A) (g : B → ℝ) (hu : ∀ V, BB (T u) V = g V) (v : A) :
    BA u v = g (T v) := by
  rw [hform]
  exact hu _

lemma sol_iff {g : B → ℝ} {k : A → ℝ} (hk : ∀ v, g (T v) = k v) (u : A) :
    (∀ v, BA u v = k v) ↔ ∀ V, BB (T u) V = g V :=
  ⟨fun h => forwards T hform u g fun v => (h v).trans (hk v).symm,
    fun h v => (backwards T hform u g h v).trans (hk v)⟩

omit hform in
lemma existsUnique_iff {P : A → Prop} {Q : B → Prop} (hPQ : ∀ u, P u ↔ Q (T u)) :
    (∃! u, P u) ↔ ∃! U, Q U := by
  constructor
  · rintro ⟨u, hu, huniq⟩
    refine ⟨T u, (hPQ u).1 hu, fun V hV => ?_⟩
    have := huniq (T.symm V) ((hPQ _).2 (by simpa using hV))
    rw [← this]
    simp
  · rintro ⟨U, hU, huniq⟩
    refine ⟨T.symm U, (hPQ _).2 (by simpa using hU), fun u hu => ?_⟩
    have := huniq (T u) ((hPQ u).1 hu)
    rw [← this]
    simp

omit hform in
lemma dual_aux (f : StrongDual ℝ A) (v : A) :
    (f.comp T.symm.toContinuousLinearMap) (T v) = f v := by
  simp

lemma isCoercive (h : IsCoercive BB) : IsCoercive BA := by
  obtain ⟨C, hC, hco⟩ := h
  obtain ⟨K, hK, hKle⟩ := exists_norm_le T
  refine ⟨C / K ^ 2, by positivity, fun u => ?_⟩
  have h1 : ‖u‖ * ‖u‖ ≤ K ^ 2 * (‖T u‖ * ‖T u‖) := by
    have := mul_self_le_mul_self (norm_nonneg u) (hKle u)
    calc ‖u‖ * ‖u‖ ≤ (K * ‖T u‖) * (K * ‖T u‖) := this
      _ = _ := by ring
  have h2 := hco (T u)
  rw [hform]
  calc C / K ^ 2 * ‖u‖ * ‖u‖ = C / K ^ 2 * (‖u‖ * ‖u‖) := by ring
    _ ≤ C / K ^ 2 * (K ^ 2 * (‖T u‖ * ‖T u‖)) := by gcongr
    _ = C * ‖T u‖ * ‖T u‖ := by field_simp
    _ ≤ _ := h2

lemma fredholm_alternative
    (h : (∃ U : B, U ≠ 0 ∧ ∀ V, BB U V = 0) ∨
      ∀ f : StrongDual ℝ B, ∃! U, ∀ V, BB U V = f V) :
    (∃ u : A, u ≠ 0 ∧ ∀ v, BA u v = 0) ∨ ∀ f : StrongDual ℝ A, ∃! u, ∀ v, BA u v = f v := by
  rcases h with ⟨U, hU, h0⟩ | h
  · refine Or.inl ⟨T.symm U, by simpa using hU, fun v => ?_⟩
    rw [hform, ContinuousLinearEquiv.apply_symm_apply]
    exact h0 _
  · refine Or.inr fun f => ?_
    refine (existsUnique_iff T (P := fun u => ∀ v, BA u v = f v)
      (Q := fun U => ∀ V, BB U V = (f.comp T.symm.toContinuousLinearMap) V) fun u => ?_).2
      (h (f.comp T.symm.toContinuousLinearMap))
    exact sol_iff T hform (dual_aux T f) u

lemma unique_imp_exists
    (h : (∀ U : B, (∀ V, BB U V = 0) → U = 0) →
      ∀ f : StrongDual ℝ B, ∃! U, ∀ V, BB U V = f V)
    (huniq : ∀ u : A, (∀ v, BA u v = 0) → u = 0) (f : StrongDual ℝ A) :
    ∃! u, ∀ v, BA u v = f v := by
  refine (existsUnique_iff T (P := fun u => ∀ v, BA u v = f v)
    (Q := fun U => ∀ V, BB U V = (f.comp T.symm.toContinuousLinearMap) V) fun u => ?_).2
    (h (fun U hU => ?_) (f.comp T.symm.toContinuousLinearMap))
  · exact sol_iff T hform (dual_aux T f) u
  · have h0 := huniq (T.symm U) (fun v => by
      rw [hform, ContinuousLinearEquiv.apply_symm_apply]
      exact hU _)
    simpa using congrArg T h0

lemma solvable_iff
    (h : ∀ f : StrongDual ℝ B, (∃ U, ∀ V, BB U V = f V) ↔
      ∀ W, (∀ V, BB V W = 0) → f W = 0) (f : StrongDual ℝ A) :
    (∃ u, ∀ v, BA u v = f v) ↔ ∀ w, (∀ v, BA v w = 0) → f w = 0 := by
  have h' := h (f.comp T.symm.toContinuousLinearMap)
  constructor
  · rintro ⟨u, hu⟩ w hw
    have h1 := h'.1 ⟨T u, (sol_iff T hform (dual_aux T f) u).1 hu⟩ (T w) (fun V => by
      have := hw (T.symm V)
      rw [hform] at this
      simpa using this)
    simpa using h1
  · intro hf
    obtain ⟨U, hU⟩ := h'.2 (fun W hW => by
      have := hf (T.symm W) (fun v => by
        rw [hform]
        simpa using hW (T v))
      simpa using this)
    exact ⟨T.symm U, (sol_iff T hform (g := fun V => (f.comp T.symm.toContinuousLinearMap) V)
      (dual_aux T f) _).2 (by simpa using hU)⟩

variable (Q : L₁ ≃ₗᵢ[ℝ] L₂) (eA : A → L₁) (eB : B → L₂) (heA : ∀ u, eB (T u) = Q (eA u))
include heA

lemma sol_iff_inner (lam : ℝ) (f : L₁) (u : A) :
    (∀ v, BA u v = lam * ⟪eA u, eA v⟫ + ⟪f, eA v⟫) ↔
      ∀ V, BB (T u) V = lam * ⟪eB (T u), eB V⟫ + ⟪Q f, eB V⟫ :=
  sol_iff T hform (g := fun V => lam * ⟪eB (T u), eB V⟫ + ⟪Q f, eB V⟫)
    (fun v => by
      simp only [heA, LinearIsometryEquiv.inner_map_map]) u

lemma sol_iff_inner' (f : L₁) (u : A) :
    (∀ v, BA u v = ⟪f, eA v⟫) ↔ ∀ V, BB (T u) V = ⟪Q f, eB V⟫ :=
  sol_iff T hform (g := fun V => ⟪Q f, eB V⟫)
    (fun v => by
      simp only [heA, LinearIsometryEquiv.inner_map_map]) u

lemma notMem_iff (lam : ℝ) :
    (∀ f' : L₂, ∃! U : B, ∀ V, BB U V = lam * ⟪eB U, eB V⟫ + ⟪f', eB V⟫) ↔
      ∀ f : L₁, ∃! u : A, ∀ v, BA u v = lam * ⟪eA u, eA v⟫ + ⟪f, eA v⟫ := by
  constructor
  · intro h f
    exact (existsUnique_iff T (P := fun u => ∀ v, BA u v = lam * ⟪eA u, eA v⟫ + ⟪f, eA v⟫)
      (Q := fun U => ∀ V, BB U V = lam * ⟪eB U, eB V⟫ + ⟪Q f, eB V⟫)
      (fun u => sol_iff_inner T hform Q eA eB heA lam f u)).2 (h (Q f))
  · intro h f'
    obtain ⟨f, rfl⟩ := Q.surjective f'
    exact (existsUnique_iff T (P := fun u => ∀ v, BA u v = lam * ⟪eA u, eA v⟫ + ⟪f, eA v⟫)
      (Q := fun U => ∀ V, BB U V = lam * ⟪eB U, eB V⟫ + ⟪Q f, eB V⟫)
      (fun u => sol_iff_inner T hform Q eA eB heA lam f u)).1 (h f)

lemma resolvent {lam C : ℝ}
    (h : ∀ (f' : L₂) (U : B), (∀ V, BB U V = lam * ⟪eB U, eB V⟫ + ⟪f', eB V⟫) →
      ‖eB U‖ ≤ C * ‖f'‖) (f : L₁) (u : A)
    (hu : ∀ v, BA u v = lam * ⟪eA u, eA v⟫ + ⟪f, eA v⟫) : ‖eA u‖ ≤ C * ‖f‖ := by
  have := h (Q f) (T u) ((sol_iff_inner T hform Q eA eB heA lam f u).1 hu)
  rwa [heA, Q.norm_map, Q.norm_map] at this

lemma weak_solution {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ f' : L₂, (∃! U : B, ∀ V, BB U V = ⟪f', eB V⟫) ∧
      ∀ U : B, (∀ V, BB U V = ⟪f', eB V⟫) → ‖U‖ ≤ M * ‖f'‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : L₁, (∃! u : A, ∀ v, BA u v = ⟪f, eA v⟫) ∧
      ∀ u : A, (∀ v, BA u v = ⟪f, eA v⟫) → ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨K, hK, hKle⟩ := exists_norm_le T
  refine ⟨K * M, by positivity, fun f => ⟨?_, fun u hu => ?_⟩⟩
  · exact (existsUnique_iff T (P := fun u => ∀ v, BA u v = ⟪f, eA v⟫)
      (Q := fun U => ∀ V, BB U V = ⟪Q f, eB V⟫)
      (fun u => sol_iff_inner' T hform Q eA eB heA f u)).2 (h (Q f)).1
  · have h1 := (h (Q f)).2 (T u) ((sol_iff_inner' T hform Q eA eB heA f u).1 hu)
    rw [Q.norm_map] at h1
    calc ‖u‖ ≤ K * ‖T u‖ := hKle u
      _ ≤ K * (M * ‖f‖) := mul_le_mul_of_nonneg_left h1 hK.le
      _ = K * M * ‖f‖ := by ring

omit heA [InnerProductSpace ℝ L₁] [InnerProductSpace ℝ L₂] in
lemma garding {l γ : ℝ} (hl : 0 < l) (eA' : A → L₁) (eB' : B → L₂)
    (heA' : ∀ u, ‖eB' (T u)‖ = ‖eA' u‖)
    (h : ∀ U : B, l / 2 * ‖U‖ ^ 2 ≤ BB U U + γ * ‖eB' U‖ ^ 2) :
    ∃ β γ' : ℝ, 0 < β ∧ ∀ u : A, β * ‖u‖ ^ 2 ≤ BA u u + γ' * ‖eA' u‖ ^ 2 := by
  obtain ⟨K, hK, hKle⟩ := exists_norm_le T
  refine ⟨l / 2 / K ^ 2, γ, by positivity, fun u => ?_⟩
  have h1 : ‖u‖ ^ 2 ≤ K ^ 2 * ‖T u‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hKle u) 2
  have h2 := h (T u)
  rw [heA', ← hform] at h2
  calc l / 2 / K ^ 2 * ‖u‖ ^ 2 ≤ l / 2 / K ^ 2 * (K ^ 2 * ‖T u‖ ^ 2) := by gcongr
    _ = l / 2 * ‖T u‖ ^ 2 := by field_simp
    _ ≤ _ := h2

end Transport

namespace Transport

/-- **Spectral transfer.** If the solution operator of a coercive symmetric form on a Hilbert space
`H` has eigenspaces spanning `L₂`, and `A ≃L H` intertwines the forms and the embeddings up to a
unitary `L₁ ≃ L₂`, then the solution operator of the form on `A`, defined by its action on data,
has eigenspaces spanning `L₁`. -/
lemma spectral {A H L₁ L₂ : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup L₁] [InnerProductSpace ℝ L₁] [CompleteSpace L₁]
    [NormedAddCommGroup L₂] [InnerProductSpace ℝ L₂] [CompleteSpace L₂]
    (T : A ≃L[ℝ] H) {BA : A →L[ℝ] A →L[ℝ] ℝ} {BB : H →L[ℝ] H →L[ℝ] ℝ}
    (hform : ∀ u v, BA u v = BB (T u) (T v)) (Q : L₁ ≃ₗᵢ[ℝ] L₂) (eA : A → L₁)
    (eB : H →L[ℝ] L₂) (heA : ∀ u, eB (T u) = Q (eA u)) (hco : IsCoercive BB)
    (hspec : (⨆ m : ℝ, Module.End.eigenspace
      (Variational.solOp eB BB hco : Module.End ℝ L₂) m)ᗮ = ⊥) :
    ∃ G : L₁ →L[ℝ] L₁, (∀ f, ∃ u : A, (∀ v, BA u v = ⟪f, eA v⟫) ∧ G f = eA u) ∧
      (⨆ m : ℝ, Module.End.eigenspace (G : Module.End ℝ L₁) m)ᗮ = ⊥ := by
  let G : L₁ →L[ℝ] L₁ :=
    (Q.symm.toContinuousLinearEquiv : L₂ →L[ℝ] L₁).comp
      ((Variational.solOp eB BB hco).comp (Q.toContinuousLinearEquiv : L₁ →L[ℝ] L₂))
  have hG : ∀ f, G f = Q.symm (Variational.solOp eB BB hco (Q f)) := fun f => rfl
  refine ⟨G, fun f => ?_, ?_⟩
  · set U := hco.continuousLinearEquivOfBilin.symm (eB.adjoint (Q f)) with hU
    have hBU : ∀ V, BB U V = ⟪Q f, eB V⟫ := fun V => by
      rw [← hco.continuousLinearEquivOfBilin_apply, hU, ContinuousLinearEquiv.apply_symm_apply,
        ContinuousLinearMap.adjoint_inner_left]
    refine ⟨T.symm U, fun v => ?_, ?_⟩
    · have := (sol_iff_inner' T hform Q eA (⇑eB) heA f (T.symm U)).2 (fun V => by
        rw [ContinuousLinearEquiv.apply_symm_apply]; exact hBU V) v
      exact this
    · rw [hG, Variational.solOp_apply, ← hU, ← ContinuousLinearEquiv.apply_symm_apply T U,
        heA, LinearIsometryEquiv.symm_apply_apply]
      simp
  · rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : Q x ∈ (⨆ m : ℝ, Module.End.eigenspace
        (Variational.solOp eB BB hco : Module.End ℝ L₂) m)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro y hy
      have hle : (⨆ m : ℝ, Module.End.eigenspace
          (Variational.solOp eB BB hco : Module.End ℝ L₂) m) ≤
          (⨆ m : ℝ, Module.End.eigenspace (G : Module.End ℝ L₁) m).comap
            Q.symm.toLinearEquiv.toLinearMap := by
        refine iSup_le fun m y' hy' => ?_
        rw [Submodule.mem_comap]
        refine Submodule.mem_iSup_of_mem m ?_
        rw [Module.End.mem_eigenspace_iff] at hy' ⊢
        change G (Q.symm y') = m • Q.symm y'
        rw [hG, LinearIsometryEquiv.apply_symm_apply]
        have : Variational.solOp eB BB hco y' = m • y' := hy'
        rw [this, map_smul]
      have hy' := Submodule.mem_comap.1 (hle hy)
      have h0 := (Submodule.mem_orthogonal _ _).1 hx _ hy'
      calc ⟪y, Q x⟫ = ⟪Q (Q.symm y), Q x⟫ := by rw [LinearIsometryEquiv.apply_symm_apply]
        _ = ⟪Q.symm y, x⟫ := Q.inner_map_map _ _
        _ = 0 := by simpa using h0
    rw [hspec] at hmem
    have : Q x = 0 := (Submodule.mem_bot ℝ).1 hmem
    simpa using this

end Transport

variable (μ) in
/-- The isometry `L²(Ω) ≃ L²(L '' Ω)` along the measure-preserving map `toEuclidean`. -/
def lpEquiv (Ω : Set E) :
    Lp ℝ 2 (μ.restrict Ω) ≃ₗᵢ[ℝ] Lp ℝ 2 ((μ.map 𝓛).restrict (𝓛 '' Ω)) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℝ (E := ℝ) (p := 2) 𝓛'
      (measurePreserving_symm_restrict_image 𝓛 μ Ω))
    (fun g => by
      refine ⟨Lp.compMeasurePreserving 𝓛 (measurePreserving_restrict_image 𝓛 μ Ω) g, ?_⟩
      refine Lp.ext ?_
      have h1 := Lp.coeFn_compMeasurePreserving
        (Lp.compMeasurePreserving 𝓛 (measurePreserving_restrict_image 𝓛 μ Ω) g)
        (measurePreserving_symm_restrict_image 𝓛 μ Ω)
      have h2 := (measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving g (measurePreserving_restrict_image 𝓛 μ Ω))
      filter_upwards [h1, h2] with y a b
      simpa using a.trans b)

variable (μ) in
omit [μ.IsAddHaarMeasure] in
/-- `lpEquiv` is composition with `toEuclidean.symm`. -/
lemma lpEquiv_apply (Ω : Set E) (f : Lp ℝ 2 (μ.restrict Ω)) :
    lpEquiv μ Ω f =
      Lp.compMeasurePreserving 𝓛' (measurePreserving_symm_restrict_image 𝓛 μ Ω) f := rfl


namespace FullEllipticOp

variable (Op : FullEllipticOp μ) (Ω : Set E)

lemma embL2_transferEquiv (u : W1p0 2 μ Ω) :
    H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω u) = lpEquiv μ Ω (W1p0.fnL u) := by
  rw [lpEquiv_apply]
  refine Lp.ext ?_
  have h1 := W1p0.fnL_mapEquiv 𝓛 u
  have h2 := Lp.coeFn_compMeasurePreserving (W1p0.fnL u)
    (measurePreserving_symm_restrict_image 𝓛 μ Ω)
  filter_upwards [h1, h2] with y a b
  exact a.trans b.symm

lemma norm_embL2_transferEquiv (u : W1p0 2 μ Ω) :
    ‖H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) (transferEquiv μ Ω u)‖ = ‖W1p0.fnL u‖ := by
  rw [embL2_transferEquiv]
  exact (lpEquiv μ Ω).norm_map _

/-- **Coercivity transfers** from the transferred operator to `W₀^{1,2}(Ω)`. -/
lemma isCoercive_formOn_of_transfer
    (h : IsCoercive (Op.transfer.formOn (𝓛 '' Ω) (H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω)))) :
    IsCoercive (Op.formOn Ω) :=
  Transport.isCoercive (transferEquiv μ Ω) (formOn_transfer Op Ω) h

variable {Ω}

/-- **Gårding inequality.** There are constants `β > 0` and `γ` with
`β ‖U‖² ≤ B[U, U] + γ ‖u‖²_{L²}` on `W₀^{1,2}(Ω)`. The constants are existential since the
transfer changes the `W₀^{1,2}` norm by an equivalence of unspecified constant. -/
theorem garding (Ω : Set E) : ∃ β γ : ℝ, 0 < β ∧ ∀ U : W1p0 2 μ Ω,
    β * ‖U‖ ^ 2 ≤ Op.formOn Ω U U + γ * ‖W1p0.fnL U‖ ^ 2 :=
  Transport.garding (transferEquiv μ Ω) (formOn_transfer Op Ω) Op.transfer.lam_pos
    (fun u => W1p0.fnL u)
    (fun U : H1Graph.H01 (μ.map 𝓛) (𝓛 '' Ω) => H1Graph.fnL (U : H1Graph (μ.map 𝓛) (𝓛 '' Ω)))
    (norm_embL2_transferEquiv Ω) (Op.transfer.garding (𝓛 '' Ω))

/-- **Existence, uniqueness and a bound on a bounded set, `L²` datum.** If the drift vanishes
and the zeroth-order coefficient is nonnegative on `Ω`, then for every `f ∈ L²(Ω)` the problem
`B[u, v] = ⟪f, v⟫` has a unique solution `u ∈ W₀^{1,2}(Ω)`, and every solution obeys
`‖u‖ ≤ C ‖f‖`. The constant `C ≥ 0` depends only on `Ω`, `Op` and `μ`; it is existential
since the transfer changes the `W₀^{1,2}` norm. -/
theorem weak_solution_of_nonneg_zeroth_of_bounded [Nontrivial E]
    (hΩb : Bornology.IsBounded Ω) (hb : ∀ᵐ x ∂μ.restrict Ω, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      (∃! u : W1p0 2 μ Ω, ∀ v, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫) ∧
      ∀ u : W1p0 2 μ Ω, (∀ v, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫) → ‖u‖ ≤ C * ‖f‖ := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  have hb' : ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω), Op.transfer.b y = 0 := by
    filter_upwards [(measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae hb]
      with y hy
    simp [transfer, hy]
  have hc' : ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω), 0 ≤ Op.transfer.c y := by
    filter_upwards [(measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae hc]
      with y hy
    simpa [transfer] using hy
  obtain ⟨CP, hCP, hex⟩ :=
    DivForm.FullEllipticOp.weak_solution_of_nonneg_zeroth_of_bounded Op.transfer
      (isBounded_image hΩb) hb' hc'
  have hl := Op.transfer.lam_pos
  exact Transport.weak_solution (transferEquiv μ Ω) (formOn_transfer Op Ω) (lpEquiv μ Ω)
    (fun u => W1p0.fnL u) (fun U => H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) U)
    (embL2_transferEquiv Ω) (M := (CP + 1) / Op.transfer.lam) (by positivity) hex

/-- **Fredholm alternative on a bounded set.** Either the homogeneous weak problem has a nonzero
solution, or `B[u, ·] = f` has a unique solution for every continuous functional `f`. -/
theorem fredholm_alternative_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) :
    (∃ u : W1p0 2 μ Ω, u ≠ 0 ∧ ∀ v, Op.formOn Ω u v = 0) ∨
      ∀ f : StrongDual ℝ (W1p0 2 μ Ω), ∃! u, ∀ v, Op.formOn Ω u v = f v :=
  Transport.fredholm_alternative (transferEquiv μ Ω) (formOn_transfer Op Ω)
    (Op.transfer.fredholm_alternative_of_bounded_haar (measurableSet_image hΩm)
      (isBounded_image hΩb))

/-- If the homogeneous weak problem on a bounded set has only the trivial solution, then
`B[u, ·] = f` has a unique solution for every continuous functional `f`. -/
theorem fredholm_unique_imp_exists_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    (huniq : ∀ u : W1p0 2 μ Ω, (∀ v, Op.formOn Ω u v = 0) → u = 0)
    (f : StrongDual ℝ (W1p0 2 μ Ω)) :
    ∃! u, ∀ v, Op.formOn Ω u v = f v :=
  Transport.unique_imp_exists (transferEquiv μ Ω) (formOn_transfer Op Ω)
    (fun hu f' => Op.transfer.fredholm_unique_imp_exists_of_bounded_haar
      (measurableSet_image hΩm) (isBounded_image hΩb) hu f') huniq f

/-- **Solvability criterion on a bounded set.** `B[u, ·] = f` has a solution exactly when `f`
annihilates every weak solution of the transpose problem. -/
theorem solvable_iff_orthogonal_transpose_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (f : StrongDual ℝ (W1p0 2 μ Ω)) :
    (∃ u, ∀ v, Op.formOn Ω u v = f v) ↔
      ∀ w, (∀ v, Op.formOn Ω v w = 0) → f w = 0 :=
  Transport.solvable_iff (transferEquiv μ Ω) (formOn_transfer Op Ω)
    (fun f' => Op.transfer.solvable_iff_orthogonal_transpose_of_bounded_haar
      (measurableSet_image hΩm) (isBounded_image hΩb) f') f

variable (Ω) in
/-- The exceptional set of the operator on `Ω`: the exceptional set of the transferred operator
on `toEuclidean '' Ω`. By `notMem_sigmaSet_iff_solvable_of_bounded_haar`, for bounded measurable
`Ω` a real `lam` lies outside it exactly when `B[u, ·] = lam ⟪u, ·⟫ + ⟪f, ·⟫` has a unique
solution `u ∈ W₀^{1,2}(Ω)` for every `f ∈ L²(Ω)`. -/
def sigmaSet : Set ℝ := Op.transfer.sigmaSet (𝓛 '' Ω)

/-- The `Σ`-membership characterisation on a bounded set. -/
theorem notMem_sigmaSet_iff_solvable_of_bounded_haar (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (lam : ℝ) :
    lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
      ∃! u : W1p0 2 μ Ω, ∀ v, Op.formOn Ω u v =
        lam * ⟪W1p0.fnL u, W1p0.fnL v⟫ + ⟪f, W1p0.fnL v⟫ :=
  (Op.transfer.notMem_sigmaSet_iff_solvable_of_bounded_haar
    (measurableSet_image hΩm) (isBounded_image hΩb) lam).trans
    (Transport.notMem_iff (transferEquiv μ Ω) (formOn_transfer Op Ω) (lpEquiv μ Ω)
      (fun u => W1p0.fnL u) (fun U => H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) U)
      (embL2_transferEquiv Ω) lam)

/-- **Existence III on a bounded set.** The exceptional set is countable, meets every
`(-∞, C]` in a finite set, and `lam` lies outside it exactly when the shifted weak problem is
uniquely solvable for every `f ∈ L²(Ω)`. -/
theorem existence_three_of_bounded_haar (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    (Op.sigmaSet Ω).Countable ∧ (∀ C : ℝ, (Op.sigmaSet Ω ∩ Set.Iic C).Finite) ∧
      ∀ lam : ℝ, lam ∉ Op.sigmaSet Ω ↔ ∀ f : Lp ℝ 2 (μ.restrict Ω),
        ∃! u : W1p0 2 μ Ω, ∀ v, Op.formOn Ω u v =
          lam * ⟪W1p0.fnL u, W1p0.fnL v⟫ + ⟪f, W1p0.fnL v⟫ :=
  ⟨(Op.transfer.existence_three_of_bounded_haar (measurableSet_image hΩm)
      (isBounded_image hΩb)).1,
    (Op.transfer.existence_three_of_bounded_haar (measurableSet_image hΩm)
      (isBounded_image hΩb)).2.1,
    fun lam => Op.notMem_sigmaSet_iff_solvable_of_bounded_haar hΩm hΩb lam⟩

/-- **Boundedness of the resolvent on a bounded set.** For `lam` outside the exceptional set, the
`L²` norm of a weak solution is bounded by a constant times the norm of the right-hand side. -/
theorem resolvent_bound_of_bounded_haar (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    {lam : ℝ} (hlam : lam ∉ Op.sigmaSet Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Lp ℝ 2 (μ.restrict Ω)) (u : W1p0 2 μ Ω),
      (∀ v, Op.formOn Ω u v =
        lam * ⟪W1p0.fnL u, W1p0.fnL v⟫ + ⟪f, W1p0.fnL v⟫) →
        ‖W1p0.fnL u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, h⟩ := Op.transfer.resolvent_bound_of_bounded_haar (measurableSet_image hΩm)
    (isBounded_image hΩb) hlam
  exact ⟨C, hC, fun f u hu => Transport.resolvent (transferEquiv μ Ω) (formOn_transfer Op Ω)
    (lpEquiv μ Ω) (fun u => W1p0.fnL u) (fun U => H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω) U)
    (embL2_transferEquiv Ω) h f u hu⟩

/-- **Spectral theorem for symmetric operators on a bounded set.** For a symmetric coefficient,
no drift and a nonnegative zeroth-order coefficient, the form is coercive on `W₀^{1,2}(Ω)` and
there is a bounded operator `G` on `L²(Ω)` sending `f` to the function part of a weak solution of
`B[u, ·] = ⟪f, ·⟫`, whose eigenspaces span `L²(Ω)`.

The inner-product twin states the spanning for `Variational.solOp`, which needs an inner product
on the energy space. `W₀^{1,2}(Ω)` has none, so the solution operator is stated by its
defining property; coercivity makes the weak solution unique, so `G` is the solution operator. -/
theorem symmetric_spectral_of_bounded_haar [Nontrivial E] (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    (ha : ∀ᵐ x ∂μ, ∀ ξ η : StrongDual ℝ E, η (Op.a x ξ) = ξ (Op.a x η))
    (hb : ∀ᵐ x ∂μ, Op.b x = 0)
    (hc : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ Op.c x) :
    IsCoercive (Op.formOn Ω) ∧ ∃ G : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] Lp ℝ 2 (μ.restrict Ω),
      (∀ f, ∃ u : W1p0 2 μ Ω, (∀ v, Op.formOn Ω u v = ⟪f, W1p0.fnL v⟫) ∧
        G f = W1p0.fnL u) ∧
      (⨆ m : ℝ, Module.End.eigenspace (G : Module.End ℝ (Lp ℝ 2 (μ.restrict Ω))) m)ᗮ = ⊥ := by
  have : Nontrivial 𝔽 := (toEuclidean (E := E)).symm.surjective.nontrivial
  have hb' : ∀ᵐ y ∂(μ.map 𝓛), Op.transfer.b y = 0 := by
    filter_upwards [measurePreserving_symm_map.quasiMeasurePreserving.ae hb] with y hy
    simp [transfer, hy]
  have hc' : ∀ᵐ y ∂(μ.map 𝓛).restrict (𝓛 '' Ω), 0 ≤ Op.transfer.c y := by
    filter_upwards [(measurePreserving_symm_restrict_image 𝓛 μ Ω).quasiMeasurePreserving.ae hc]
      with y hy
    simpa [transfer] using hy
  obtain ⟨hco', hspec⟩ := Op.transfer.symmetric_spectral_of_bounded_haar (measurableSet_image hΩm)
    (isBounded_image hΩb) (Op.transfer_adjoint ha) hb' hc'
  exact ⟨isCoercive_formOn_of_transfer Op Ω hco',
    Transport.spectral (transferEquiv μ Ω) (formOn_transfer Op Ω) (lpEquiv μ Ω)
      (fun u => W1p0.fnL u) (H1Graph.embL2 (μ.map 𝓛) (𝓛 '' Ω)) (embL2_transferEquiv Ω) hco'
      hspec⟩

end FullEllipticOp

end NormedDivForm

end EllipticPdes
