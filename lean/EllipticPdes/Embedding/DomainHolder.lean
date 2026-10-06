/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Embedding.DomainLadder

/-!
# Hölder continuity up to the boundary

The second case of the Sobolev embedding at order `k` reads the Hölder exponent off Morrey's
inequality at the exponent the ladder reaches, and states it on the closure of the domain. This
file proves that statement.

The chain has three links. The ladder of `EllipticPdes.Embedding.DomainLadder` puts the member
and its first derivatives in `L^P(Ω)` for a `P` above the dimension;
`EllipticPdes.Extension.exists_extension_subset_bound` puts them on the whole space with the
same bound; and `morrey_ball` on a ball containing the closure of the domain produces the
continuous representative, whose Hölder seminorm is bounded by the `L^P` norms of the extended
gradient. Restricting the representative to the closure of the domain is the last step, and it
is where the conclusion reaches the boundary, which the interior statements of
`EllipticPdes.Embedding.HolderGeneral` do not.

## Supremum as well as seminorm

The `C^{0,γ}` norm of the cited statement is the supremum plus the Hölder seminorm, and Morrey
supplies the seminorm alone. The supremum comes from the support clause of the extension: the
extension vanishes outside a ball the closure of the domain sits inside, the representative is
therefore zero somewhere in the larger ball Morrey runs on, and the estimate against that point
bounds the representative everywhere by the seminorm times a power of the diameter. That power
depends on the two radii and the exponent alone, so one constant states both halves.

## Main declarations

* `EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain`: clause (ii) of the
  embedding on the closure of the domain, with a constant taken before the family.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem IV.2.3 case
(ii); L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.3 Theorem 6 clause (ii).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Extension (HasC1Boundary exists_extension_subset_bound)

variable {d : ℕ}

/-- A Hölder function that vanishes at a point `z` is bounded there by its constant times a
power of the distance. -/
theorem norm_le_of_holderOnWith_of_eq_zero {X : Type*} [PseudoMetricSpace X] {C γ : ℝ≥0}
    {w : X → ℝ} {S : Set X} (h : HolderOnWith C γ w S) {z y : X} (hz : z ∈ S) (hy : y ∈ S)
    (hw : w z = 0) {D : ℝ} (hD : dist y z ≤ D) : ‖w y‖ ≤ C * D ^ (γ : ℝ) := by
  have := h.dist_le hy hz
  rw [hw, Real.dist_eq, sub_zero] at this
  exact this.trans (by gcongr)

/-- An a.e. vanishing function vanishes at some point of every nonempty open set. -/
theorem exists_apply_eq_zero_of_ae_eq_zero {E : Type*} [TopologicalSpace E] {m : MeasurableSpace E}
    [BorelSpace E] {μ : Measure E} [μ.IsOpenPosMeasure] {w : E → ℝ} {V : Set E} (hV : IsOpen V)
    (hne : V.Nonempty) (h : ∀ᵐ x ∂μ.restrict V, w x = 0) : ∃ z ∈ V, w z = 0 := by
  have : (ae (μ.restrict V)).NeBot := ae_neBot.mpr (by
    rw [Ne, Measure.restrict_eq_zero]; exact (hV.measure_pos μ hne).ne')
  obtain ⟨z, hz, hz0⟩ := (h.and (ae_restrict_mem hV.measurableSet)).exists
  exact ⟨z, hz0, hz⟩

/-- **Hölder representative of an extended class.** For `P > d` there is one constant such that a
class `u` on a bounded domain with `C¹` boundary, whose weak gradient `g` has all of `u` and `gₖ`
bounded by `B` in `L^P(Ω)`, has a representative that is bounded by `C B` and Hölder with
constant `C B` on the closure of the domain. The class is extended across the boundary into a ball,
Morrey runs on a larger ball, and the extension vanishes somewhere in the annulus, which bounds
the representative by its seminorm times a power of the diameter. -/
theorem exists_holderOnWith_of_extension (hd : 0 < d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hC1 : HasC1Boundary Ω) {P : ℝ≥0}
    (hP1 : 1 ≤ P) (hPd : (d : ℝ) < (P : ℝ)) :
    ∃ C : ℝ≥0, ∀ (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
      (B : ℝ≥0), IntegrableOn u Ω volume → (∀ k, IntegrableOn (g k) Ω volume) →
      HasWeakGradOn Ω u g → eLpNorm u P (volume.restrict Ω) ≤ B →
      (∀ k, eLpNorm (g k) P (volume.restrict Ω) ≤ B) →
      ∃ w : EuclideanSpace ℝ (Fin d) → ℝ, w =ᵐ[volume.restrict Ω] u ∧
        (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * B : ℝ≥0) : ℝ)) ∧
        HolderOnWith (C * B) (morreyExponent d (P : ℝ)) w (closure Ω) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; exact hd)
  obtain ⟨rb, rb', hrb, hrbb', hcl, z, hz, hzn⟩ := exists_balls_around_isBounded hΩb
  obtain ⟨KE, hKE⟩ := exists_extension_subset_bound hd hΩopen hΩb hC1
    (isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin d))) (ε := rb)) hcl
    (p := (P : ℝ≥0∞)) (by exact_mod_cast hP1)
  obtain ⟨Cm, hCm⟩ := morrey_ball hd hPd (0 : EuclideanSpace ℝ (Fin d)) (hrb.trans hrbb')
  set Cb : ℝ≥0 := Cm * (d * (KE * (d + 1))) with hCb
  set Cd : ℝ≥0 := ((2 * rb') ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ)).toNNReal with hCd
  refine ⟨Cb + Cb * Cd, fun u g B hui hgi hwg hu hg => ?_⟩
  obtain ⟨U, G, hwgU, -, hsuppU, hUint, hGint, hag, -, hGb⟩ := hKE u g hui hgi hwg
  have hGB : ∀ k, eLpNorm (G k) (P : ℝ≥0∞) volume ≤ ((KE * ((d + 1) * B) : ℝ≥0) : ℝ≥0∞) :=
    fun k => (hGb k).trans (by
      push_cast; exact mul_le_mul_right (add_sum_le_of_le hu hg) _)
  obtain ⟨w, hwae, hwhol⟩ := hCm U G hUint.integrableOn (fun k => by
    rw [ENNReal.ofReal_coe_nnreal]
    have hm : MemLp (G k) (P : ℝ≥0∞) volume := lt_of_le_of_lt (hGB k) ENNReal.coe_lt_top
    exact hm.restrict _)
    (hwgU.mono (subset_univ _))
  have hhol : HolderOnWith (Cb * B) (morreyExponent d (P : ℝ)) w (ball 0 rb') := by
    refine hwhol.mono_const ?_
    calc _ ≤ Cm * (d * (KE * ((d + 1) * B))) := mul_le_mul_right (sum_toNNReal_eLpNorm_le
        fun k => by
          rw [ENNReal.ofReal_coe_nnreal]
          exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hGB k)) _
      _ = Cb * B := by rw [hCb]; ring
  -- the representative vanishes in the annulus, outside the support of the extension
  obtain ⟨z₀, hz₀V, hz₀⟩ := exists_apply_eq_zero_of_ae_eq_zero (μ := volume) (w := w)
    (V := ball 0 rb' \ tsupport U) (isOpen_ball.sdiff (isClosed_tsupport U))
    ⟨z, hz, fun hc => hzn (hsuppU hc)⟩ (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hwae,
        ae_restrict_mem (isOpen_ball.sdiff (isClosed_tsupport U)).measurableSet] with x hx hxV
      rw [hx, image_eq_zero_of_notMem_tsupport hxV.2])
  have hsup : ∀ y ∈ closure Ω, ‖w y‖ ≤ (((Cb + Cb * Cd) * B : ℝ≥0) : ℝ) := fun y hy => by
    have hyb : y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) rb' := ball_subset_ball hrbb'.le (hcl hy)
    have hyz : dist y z₀ ≤ 2 * rb' := by
      have := mem_ball.mp hyb
      have := mem_ball.mp hz₀V.1
      rw [dist_comm z₀] at *
      linarith [dist_triangle y 0 z₀]
    refine (norm_le_of_holderOnWith_of_eq_zero hhol hz₀V.1 hyb hz₀ hyz).trans ?_
    have hCdc : ((Cd : ℝ≥0) : ℝ) = (2 * rb') ^ ((morreyExponent d (P : ℝ) : ℝ≥0) : ℝ) := by
      rw [hCd, Real.coe_toNNReal _ (Real.rpow_nonneg (by linarith) _)]
    rw [← hCdc]
    push_cast
    nlinarith [Cb.coe_nonneg, B.coe_nonneg, Cd.coe_nonneg]
  refine ⟨w, ?_, hsup, ?_⟩
  · refine Filter.EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset
      (subset_closure.trans (hcl.trans (ball_subset_ball hrbb'.le))) hwae) ?_
    exact (ae_restrict_iff' hΩopen.measurableSet).mpr
      (Filter.Eventually.of_forall fun y hy => hag y hy)
  · exact (hhol.mono (hcl.trans (ball_subset_ball hrbb'.le))).mono_const
      (mul_le_mul_left le_self_add _)

/-- **Clause (ii) of the embedding on a bounded domain with `C¹` boundary.** One constant,
depending on the domain, the dimension, the base exponent, the rung count and the landing
exponent, bounds both the supremum and the Hölder seminorm on the closure of the domain of a
representative of every member by a uniform `L^{p₀}` bound on the family. The Hölder exponent is
Morrey's `1 - d/P`, which `EllipticPdes.Embedding.morreyExponent_eq_ladder` identifies with the
`⌊n/p⌋ + 1 - n/p` of the cited statement at the landing exponent. -/
theorem exists_const_holderOnWith_of_gradClosed_domain (hd : 1 < d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩopen : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hC1 : HasC1Boundary Ω) (ι : Type*) {p₀ P : ℝ≥0} (hp₀ : 1 ≤ p₀) {s : ℕ}
    (hsd : (p₀ : ℝ) * s ≤ (d : ℝ)) (hp₀P : p₀ ≤ P) (hPd : (d : ℝ) < (P : ℝ))
    (hPs : (p₀ : ℝ)⁻¹ - (s : ℝ) * (d : ℝ)⁻¹ ≤ (P : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {F : ι → EuclideanSpace ℝ (Fin d) → ℝ} {nxt : ι → Fin d → ι}
      {dep : ι → ℕ} {m : ℕ}, (∀ i k, dep (nxt i k) ≤ dep i + 1) →
      (∀ i, dep i < m → HasWeakGradOn Ω (F i) (fun k => F (nxt i k))) →
      (∀ i, dep i ≤ m → MemLp (F i) p₀ (volume.restrict Ω)) →
      ∀ M : ℝ≥0, (∀ j, dep j ≤ m → eLpNorm (F j) p₀ (volume.restrict Ω) ≤ (M : ℝ≥0∞)) →
      ∀ i, dep i + 1 + s ≤ m →
        ∃ w : EuclideanSpace ℝ (Fin d) → ℝ,
          w =ᵐ[volume.restrict Ω] F i ∧
            (∀ y ∈ closure Ω, ‖w y‖ ≤ ((C * M : ℝ≥0) : ℝ)) ∧
            HolderOnWith (C * M) (morreyExponent d (P : ℝ)) w (closure Ω) := by
  obtain ⟨K, hK⟩ := exists_const_memLp_of_gradClosed_domain hd hΩopen hΩb hC1 hp₀ ι s hsd hp₀P hPs
  obtain ⟨CE, hCE⟩ := exists_holderOnWith_of_extension (by omega) hΩopen hΩb hC1 (P := P)
    (hp₀.trans hp₀P) hPd
  refine ⟨CE * K, fun {F nxt dep m} hdep hgrad hmem M hM i hi => ?_⟩
  have := isFiniteMeasure_restrict_of_isBounded hΩb
  have hlad : ∀ j, dep j + s ≤ m → MemLp (F j) P (volume.restrict Ω) ∧
      eLpNorm (F j) P (volume.restrict Ω) ≤ ((K * M : ℝ≥0) : ℝ≥0∞) := fun j hj => by
    rw [ENNReal.coe_mul]; exact hK hdep hgrad hmem M hM j hj
  have hP1 : (1 : ℝ≥0∞) ≤ P := by exact_mod_cast hp₀.trans hp₀P
  obtain ⟨w, hwae, hwsup, hwhol⟩ := hCE (F i) (fun k => F (nxt i k)) (K * M)
    ((hlad i (by omega)).1.integrable hP1)
    (fun k => (hlad _ (by have := hdep i k; omega)).1.integrable hP1) (hgrad i (by omega))
    (hlad i (by omega)).2 (fun k => (hlad _ (by have := hdep i k; omega)).2)
  rw [← mul_assoc] at hwsup hwhol
  exact ⟨w, hwae, hwsup, hwhol⟩

end EllipticPdes.Embedding
