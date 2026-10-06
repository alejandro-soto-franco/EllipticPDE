/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.WeakGradient
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Common tools of the extension

The weak derivative along a direction `v` of any normed space, transported through an affine
automorphism that preserves the measure: translations, reflections and linear isometries are
instances of one statement. The pairs of a class and a gradient that the extension operators act
on, with the seminorm that bounds them, and the small lemmas on supports, integrability and
seminorms that the files of the extension share.

## Main declarations

* `EllipticPdes.Extension.HasWeakDerivAlong`: the weak derivative of `u` along `v` on `B`.
* `EllipticPdes.Extension.hasWeakGradOn_iff`: a weak gradient is a family of weak derivatives.
* `EllipticPdes.Extension.HasWeakDerivAlong.comp_affine`: transport through `x ↦ e x + c`.
* `EllipticPdes.Extension.HasWeakDerivAlong.sum`: a weak derivative is linear in the direction.
* `EllipticPdes.Extension.SobolevPair` and `EllipticPdes.Extension.pairNorm`: a class with its
  gradient, and the seminorm of both.
* `EllipticPdes.Extension.integral_eq_neg_integral_of_tendsto`: an integration by parts identity
  passes to a limit of bounded test functions.
* `EllipticPdes.Extension.tsupport_comp_homeomorph`: the topological support of a composite.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

noncomputable section

namespace EllipticPdes.Extension

open EllipticPdes.Embedding (HasWeakGradOn)
open EllipticPdes.Sobolev (partialD)

/-- **Seminorm of a combination with coefficients of modulus at most one.** -/
theorem eLpNorm_sum_mul_le {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {p : ENNReal} (hp : 1 ≤ p) {a : ι → ℝ} (ha : ∀ i, |a i| ≤ 1) {w : ι → α → ℝ}
    (hw : ∀ i, AEStronglyMeasurable (w i) μ) :
    eLpNorm (fun y => ∑ i, a i * w i y) p μ ≤ ∑ i, eLpNorm (w i) p μ := by
  have hfun : (fun y => ∑ i, a i * w i y) = ∑ i, fun y => a i * w i y := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun]
  refine le_trans (eLpNorm_sum_le hp) (Finset.sum_le_sum fun i _ => ?_)
  refine eLpNorm_mono_ae ((hw i).const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs (a i)]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha i)

/-! ### Pairs of a class and a gradient -/

/-- A class together with a candidate for its gradient. This is the module the extension
operator acts on. -/
abbrev SobolevPair (d : ℕ) : Type :=
  (EuclideanSpace ℝ (Fin d) → ℝ) × (Fin d → EuclideanSpace ℝ (Fin d) → ℝ)

/-- The `Lᵖ` seminorm of a class plus those of the components of its gradient. -/
def pairNorm {d : ℕ} (p : ENNReal) (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : ENNReal :=
  eLpNorm u p μ + ∑ i, eLpNorm (g i) p μ

section PairNorm

variable {d : ℕ} {p : ENNReal} {μ : Measure (EuclideanSpace ℝ (Fin d))}
  {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}

/-- The seminorm of the class is at most the pair seminorm. -/
theorem eLpNorm_le_pairNorm : eLpNorm u p μ ≤ pairNorm p μ u g := le_self_add

/-- The seminorm of one component of the gradient is at most the pair seminorm. -/
theorem eLpNorm_grad_le_pairNorm (k : Fin d) : eLpNorm (g k) p μ ≤ pairNorm p μ u g :=
  (Finset.single_le_sum (f := fun i => eLpNorm (g i) p μ) (fun _ _ => zero_le)
    (Finset.mem_univ k)).trans le_add_self

/-- The seminorm of the class and of one component of the gradient together is at most the pair
seminorm. -/
theorem eLpNorm_add_grad_le_pairNorm (k : Fin d) :
    eLpNorm u p μ + eLpNorm (g k) p μ ≤ pairNorm p μ u g :=
  add_le_add_right (Finset.single_le_sum (f := fun i => eLpNorm (g i) p μ)
    (fun _ _ => zero_le) (Finset.mem_univ k)) _

end PairNorm

/-- **Seminorm of a product with a bounded factor.** -/
theorem eLpNorm_mul_le_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f h : α → ℝ} {C : ℝ} {p : ENNReal} (hfh : AEStronglyMeasurable (fun x => f x * h x) μ)
    (hC : ∀ x, ‖h x‖ ≤ C) : eLpNorm (fun x => f x * h x) p μ ≤ ENNReal.ofReal C * eLpNorm f p μ :=
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfh (Filter.Eventually.of_forall fun x => by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)) p

/-! ### Supports and integrability -/

/-- The topological support of `f ∘ e` for a homeomorphism `e` is the preimage of that
of `f`. -/
theorem tsupport_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero Z] (e : X ≃ₜ Y) (f : Y → Z) : tsupport (f ∘ e) = e ⁻¹' tsupport f := by
  rw [tsupport, tsupport, Function.support_comp_eq_preimage, e.preimage_closure]

/-- The product of an integrable function with a continuous function of compact support is
integrable. -/
theorem _root_.MeasureTheory.IntegrableOn.mul_of_hasCompactSupport {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {B : Set X} {u h : X → ℝ}
    (hu : IntegrableOn u B μ) (hh : Continuous h) (hcs : HasCompactSupport h) :
    IntegrableOn (fun x => u x * h x) B μ := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hh
  exact hu.mul_bdd hh.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- **Chain rule for a partial derivative.** If `f` has derivative `L` at `x`, the `k`-th partial
derivative of `φ ∘ f` at `x` is the derivative of `φ` at `f x` along `L (eₖ)`. -/
theorem partialD_comp {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)} (hφ : DifferentiableAt ℝ φ (f x)) (hf : HasFDerivAt f L x)
    (k : Fin d) :
    partialD k (fun y => φ (f y)) x = fderiv ℝ φ (f x) (L (EuclideanSpace.single k (1 : ℝ))) := by
  have := (hφ.hasFDerivAt.comp x hf).fderiv
  rw [partialD, show (fun y => φ (f y)) = φ ∘ f from rfl, this]
  rfl

/-- **Dominated convergence for a product with a fixed integrable factor.** -/
theorem tendsto_setIntegral_mul {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {B : Set X} (hB : MeasurableSet B) {u : X → ℝ}
    (hu : IntegrableOn u B μ) {f : ℕ → X → ℝ} {f' : X → ℝ} (hf : ∀ n, Continuous (f n)) {C : ℝ}
    (hb : ∀ n x, ‖f n x‖ ≤ C) (hc : ∀ x ∈ B, Tendsto (fun n => f n x) atTop (𝓝 (f' x))) :
    Tendsto (fun n => ∫ x in B, u x * f n x ∂μ) atTop (𝓝 (∫ x in B, u x * f' x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => C * ‖u x‖)
    (fun n => hu.1.mul (hf n).aestronglyMeasurable) (hu.norm.const_mul C) (fun n => ?_)
    ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx => (hc x hx).const_mul (u x)))
  filter_upwards with x
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb n x) (norm_nonneg _)

/-- **Passing an integration by parts identity to a limit.** If `∫_B u F n = -∫_B g G n` for
a sequence of continuous functions `F n`, `G n` that are uniformly bounded and converge
pointwise, then the identity holds for the limits. -/
theorem integral_eq_neg_integral_of_tendsto {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} {B : Set X} (hB : MeasurableSet B) {u g : X → ℝ}
    (hu : IntegrableOn u B μ) (hg : IntegrableOn g B μ) {F G : ℕ → X → ℝ} {F' G' : X → ℝ}
    (hF : ∀ n, Continuous (F n)) (hG : ∀ n, Continuous (G n)) {N P : ℝ}
    (hFb : ∀ n x, ‖F n x‖ ≤ N) (hGb : ∀ n x, ‖G n x‖ ≤ P)
    (hFc : ∀ x ∈ B, Tendsto (fun n => F n x) atTop (𝓝 (F' x)))
    (hGc : ∀ x ∈ B, Tendsto (fun n => G n x) atTop (𝓝 (G' x)))
    (hid : ∀ n, ∫ x in B, u x * F n x ∂μ = -∫ x in B, g x * G n x ∂μ) :
    ∫ x in B, u x * F' x ∂μ = -∫ x in B, g x * G' x ∂μ :=
  tendsto_nhds_unique (tendsto_setIntegral_mul hB hu hF hFb hFc)
    (by simpa only [hid] using (tendsto_setIntegral_mul hB hg hG hGb hGc).neg)

/-- The partial derivatives of a function of compact support have compact support. -/
theorem _root_.HasCompactSupport.partialD {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : HasCompactSupport ψ) (k : Fin d) : HasCompactSupport (partialD k ψ) :=
  hψ.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))

/-- The partial derivatives of a `C¹` function are continuous. -/
theorem _root_.ContDiff.continuous_partialD {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {n : WithTop ℕ∞} (hψ : ContDiff ℝ n ψ) (hn : n ≠ 0) (k : Fin d) : Continuous (partialD k ψ) :=
  (hψ.continuous_fderiv hn).clm_apply continuous_const

/-- **Determinant of the identity plus a rank-one map.** -/
theorem _root_.LinearMap.det_id_add_smulRight {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) (v : E) :
    (LinearMap.id + f.smulRight v).det = 1 + f v := by
  let b := Module.finBasis ℝ E
  rw [← LinearMap.det_toMatrix b]
  have : LinearMap.toMatrix b b (LinearMap.id + f.smulRight v)
      = 1 + Matrix.replicateCol Unit (b.repr v) * Matrix.replicateRow Unit (fun i => f (b i)) := by
    ext i k
    simp [LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.replicateCol,
      Matrix.replicateRow, Finsupp.single_apply, eq_comm, mul_comm]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have h := congrArg f (b.sum_repr v)
  rw [map_sum] at h
  simpa [dotProduct, mul_comm] using h

/-- The product of a continuous function of compact support with an integrable function,
the continuous factor written first. -/
theorem _root_.MeasureTheory.IntegrableOn.hasCompactSupport_mul {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    {B : Set X} {u h : X → ℝ} (hu : IntegrableOn u B μ) (hh : Continuous h)
    (hcs : HasCompactSupport h) : IntegrableOn (fun x => h x * u x) B μ :=
  (hu.mul_of_hasCompactSupport hh hcs).congr (Filter.Eventually.of_forall fun _ => mul_comm _ _)

/-- **One bound for a smooth compactly supported function and for each of its partials.** -/
theorem exists_bound_with_partials {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) h) (hcs : HasCompactSupport h) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ y, ‖h y‖ ≤ C) ∧ ∀ (k : Fin d) (y : EuclideanSpace ℝ (Fin d)),
      ‖partialD k h y‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hcs.exists_bound_of_continuous hc.continuous
  choose Ck hCk using fun k => (hcs.partialD k).exists_bound_of_continuous
    (hc.continuous_partialD (by simp) k)
  have hsum0 : (0 : ℝ) ≤ ∑ k, Ck k := Finset.sum_nonneg fun k _ => (norm_nonneg _).trans (hCk k 0)
  have hC00 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0)
  refine ⟨C₀ + ∑ k, Ck k, by linarith, fun y => (hC₀ y).trans (by linarith),
    fun k y => (hCk k y).trans ?_⟩
  linarith [Finset.single_le_sum (f := fun j => Ck j)
    (fun j _ => (norm_nonneg _).trans (hCk j 0)) (Finset.mem_univ k)]

section WeakDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- **Weak derivative along a direction.** `g` is the weak derivative of `u` along `v` on `B`
when `∫_B u ∂_v φ = -∫_B g φ` for every smooth test function `φ` supported in `B`. -/
def HasWeakDerivAlong (μ : Measure E) (v : E) (B : Set E) (u g : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ B →
    ∫ x in B, u x * fderiv ℝ φ x v ∂μ = -∫ x in B, g x * φ x ∂μ

/-- A weak gradient is a family of weak derivatives along the standard directions. -/
theorem hasWeakGradOn_iff {d : ℕ} {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} :
    HasWeakGradOn B u g ↔
      ∀ k, HasWeakDerivAlong volume (EuclideanSpace.single k (1 : ℝ)) B u (g k) :=
  ⟨fun h k φ hφ hc hs => h φ hφ hc hs k, fun h φ hφ hc hs k => h k φ hφ hc hs⟩

/-- A weak derivative scales with the direction. -/
theorem HasWeakDerivAlong.smul {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ v B u g) (c : ℝ) :
    HasWeakDerivAlong μ (c • v) B u (fun x => c * g x) := by
  intro φ hφ hc hs
  have : ∀ x, u x * fderiv ℝ φ x (c • v) = c * (u x * fderiv ℝ φ x v) := fun x => by
    simp only [map_smul, smul_eq_mul]; ring
  simp_rw [this, mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ hc hs, mul_neg]

/-- **A weak derivative is linear in the direction.** For integrable `u` and integrable
derivatives, the derivative along a combination of directions is the combination of the
derivatives. -/
theorem HasWeakDerivAlong.sum [OpensMeasurableSpace E] {ι : Type*} (s : Finset ι)
    {B : Set E} {u : E → ℝ} {v : ι → E} {g : ι → E → ℝ} (c : ι → ℝ) (hu : IntegrableOn u B μ)
    (hg : ∀ i ∈ s, IntegrableOn (g i) B μ) (h : ∀ i ∈ s, HasWeakDerivAlong μ (v i) B u (g i)) :
    HasWeakDerivAlong μ (∑ i ∈ s, c i • v i) B u (fun x => ∑ i ∈ s, c i * g i x) := by
  intro φ hφ hc hs
  have hφc : Continuous φ := hφ.continuous
  have hd : ∀ w, Continuous fun x => fderiv ℝ φ x w := fun w =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hu' : ∀ i, IntegrableOn (fun x => u x * fderiv ℝ φ x (v i)) B μ := fun i =>
    hu.mul_of_hasCompactSupport (hd _) (hc.fderiv_apply (𝕜 := ℝ) _)
  have hg' : ∀ i ∈ s, IntegrableOn (fun x => g i x * φ x) B μ := fun i hi =>
    (hg i hi).mul_of_hasCompactSupport hφc hc
  have h1 : ∫ x in B, u x * fderiv ℝ φ x (∑ i ∈ s, c i • v i) ∂μ
      = ∑ i ∈ s, c i * ∫ x in B, u x * fderiv ℝ φ x (v i) ∂μ := by
    have : ∀ x, u x * fderiv ℝ φ x (∑ i ∈ s, c i • v i)
        = ∑ i ∈ s, c i * (u x * fderiv ℝ φ x (v i)) := fun x => by
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i _ => (hu' i).const_mul (c i)]
    simp_rw [integral_const_mul]
  have h2 : ∫ x in B, (∑ i ∈ s, c i * g i x) * φ x ∂μ
      = ∑ i ∈ s, c i * ∫ x in B, g i x * φ x ∂μ := by
    have : ∀ x, (∑ i ∈ s, c i * g i x) * φ x = ∑ i ∈ s, c i * (g i x * φ x) := fun x => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i hi => (hg' i hi).const_mul (c i)]
    simp_rw [integral_const_mul]
  rw [h1, h2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi φ hφ hc hs, mul_neg]

/-- **Transport of a weak derivative through an affine automorphism.** If `x ↦ e x + c`
preserves `μ` and `u` has weak derivative `g` along `e v` on `B`, then `u ∘ (e · + c)` has weak
derivative `g ∘ (e · + c)` along `v` on the preimage of `B`. -/
theorem HasWeakDerivAlong.comp_affine [BorelSpace E] (e : E ≃L[ℝ] E) (c : E)
    (hmp : MeasurePreserving (fun x => e x + c) μ μ) {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ (e v) B u g) :
    HasWeakDerivAlong μ v ((fun x => e x + c) ⁻¹' B) (fun x => u (e x + c))
      (fun x => g (e x + c)) := by
  intro φ hφ hc hs
  let S : E ≃ₜ E := (Homeomorph.subRight c).trans e.symm.toHomeomorph
  have hS : ∀ y, S y = e.symm (y - c) := fun _ => rfl
  have hSd : ∀ y, HasFDerivAt S (e.symm : E →L[ℝ] E) y := fun y => by
    exact (e.symm.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)).congr_fderiv
      (ContinuousLinearMap.comp_id _)
  have hSc : ContDiff ℝ (⊤ : ℕ∞) S :=
    e.symm.contDiff.comp (contDiff_id.sub contDiff_const)
  have hψd : ∀ y, fderiv ℝ (φ ∘ S) y (e v) = fderiv ℝ φ (S y) v := fun y => by
    rw [((hφ.differentiable (by simp) _).hasFDerivAt.comp y (hSd y)).fderiv]
    simp
  have key := h (φ ∘ S) (hφ.comp hSc) (hc.comp_homeomorph S) (by
    rw [tsupport_comp_homeomorph]
    intro y hy
    simpa [hS] using hs hy)
  simp only [hψd] at key
  have hme : MeasurableEmbedding (fun x => e x + c) :=
    (e.toHomeomorph.trans (Homeomorph.addRight c)).measurableEmbedding
  have cv := fun F : E → ℝ => hmp.setIntegral_preimage_emb hme F B
  rw [← cv, ← cv] at key
  simpa [hS] using key

/-- **Transport of a weak derivative through a linear automorphism.** -/
theorem HasWeakDerivAlong.comp_linear [BorelSpace E] (e : E ≃L[ℝ] E)
    (hmp : MeasurePreserving e μ μ) {v : E} {B : Set E} {u g : E → ℝ}
    (h : HasWeakDerivAlong μ (e v) B u g) :
    HasWeakDerivAlong μ v (e ⁻¹' B) (fun x => u (e x)) (fun x => g (e x)) := by
  simpa using h.comp_affine e 0 (by simpa using hmp)

end WeakDeriv

end EllipticPdes.Extension
