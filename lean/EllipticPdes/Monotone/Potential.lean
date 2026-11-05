/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.OperatorBackground
public import EllipticPdes.Form.BilinearForm
public import EllipticPdes.Monotone.Basic
public import EllipticPdes.Monotone.DirectMethod

/-!
# Potential operators and the variational inequality

An operator `A : X → X*` which is the Gateaux derivative of a convex functional `J` is monotone,
and a minimiser of `J` on a convex set `K` satisfies the variational inequality
`0 ≤ ⟨A u, v - u⟩` for `v` in `K`. The second argument adapts Ferreira–Gomes–Üçer
(`ferreira-2025-sol-mea-gam`, Remark 2.17, p. 12), who pass from the weak to the strong
variational inequality by testing with `(1 - t) u + t v` and letting `t → 0`. This file proves
both statements and applies the direct method to show that a coercive potential operator is onto
the dual.

The Gateaux hypothesis is `∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0`. Convexity
gives the gradient inequality `J u + ⟨A u, v - u⟩ ≤ J v`. Applied at `v` and at the midpoint of `v`
and the base point `v₀` of coercivity, it bounds `J v` below by the coercivity quotient, so that
`J - f` is coercive for every `f` in the dual.

## Main declarations

* `EllipticPdes.isMonotoneOp_of_convex_gateaux`: the Gateaux derivative of a convex functional is
  monotone.
* `EllipticPdes.variationalInequality_of_isMinOn`: a minimiser on a convex set satisfies the
  variational inequality.
* `EllipticPdes.exists_eq_of_potential`: a coercive potential monotone operator is onto the dual.
* `EllipticPdes.existsUnique_eq_of_potential`: the preimage is unique when `A` is strictly
  monotone.
* `EllipticPdes.laxMilgram_symm_of_potential`: symmetric Lax–Milgram from the potential
  `u ↦ B u u / 2`.
-/

@[expose] public section

open Filter Topology Set

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {J : X → ℝ} {A : X → StrongDual ℝ X}

/-- **Gradient inequality.** A convex function with Gateaux derivative `A` lies above its tangent:
`J u + ⟨A u, v - u⟩ ≤ J v`. The proof uses the testing argument of Ferreira–Gomes–Üçer,
Remark 2.17, p. 12: convexity along `(1 - t) u + t v`, division by `t` and the limit `t → 0`. -/
theorem gradient_inequality_of_convex_gateaux (hJc : ConvexOn ℝ univ J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) (u v : X) :
    J u + A u (v - u) ≤ J v := by
  have h := (hJ u (v - u)).tendsto_slope_zero_right
  have key : A u (v - u) ≤ J v - J u := by
    refine le_of_tendsto h ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    have hconv := hJc.2 (mem_univ u) (mem_univ v) (sub_nonneg.mpr ht.2.le) ht.1.le
      (by ring)
    have hrw : u + t • (v - u) = (1 - t) • u + t • v := by module
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul, hrw]
    rw [inv_mul_le_iff₀ ht.1]
    simp only [smul_eq_mul] at hconv
    nlinarith
  linarith

/-- **Monotonicity of a convex potential.** If `J` is convex and `A u` is its Gateaux derivative
at `u`, then `A` is monotone on the whole space. This is the classical monotonicity of the
derivative of a convex function, which follows from the gradient inequality at `u` and at `v`. -/
theorem isMonotoneOp_of_convex_gateaux (hJc : ConvexOn ℝ univ J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) :
    IsMonotoneOp univ A := by
  intro u _ v _
  have h1 := gradient_inequality_of_convex_gateaux hJc hJ u v
  have h2 := gradient_inequality_of_convex_gateaux hJc hJ v u
  have h3 : (A u - A v) (u - v) = -(A u (v - u)) - A v (u - v) := by
    simp only [sub_apply, map_sub]; ring
  rw [h3]
  linarith

/-- **Variational inequality.** A minimiser `u` of `J` on a convex set `K` satisfies
`0 ≤ ⟨A u, v - u⟩` for every `v` in `K`. The proof adapts the argument of Ferreira–Gomes–Üçer,
Remark 2.17, p. 12, which passes from the weak to the strong variational inequality by testing with
`(1 - t) u + t v` and letting `t → 0`; here the test point lies in `K` by convexity and `u` is
a minimiser of the Gateaux-differentiable `J`. -/
theorem variationalInequality_of_isMinOn
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0) {K : Set X}
    (hKc : Convex ℝ K) {u : X} (hu : u ∈ K) (hmin : IsMinOn J K u) :
    ∀ v ∈ K, 0 ≤ A u (v - u) := by
  intro v hv
  have h := (hJ u (v - u)).tendsto_slope_zero_right
  refine ge_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  have hmem : u + t • (v - u) ∈ K := by
    have := hKc hu hv (sub_nonneg.mpr ht.2.le) ht.1.le (by ring)
    convert this using 1
    module
  have := hmin hmem
  simp only [mem_ofPred_eq] at this
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr this)

/-- **Lower bound for a coercive potential.** If `A` is coercive on the whole space and `J` is a
convex potential of `A`, then `J - f` tends to infinity at infinity for every `f` in the dual. The
bound applies the gradient inequality at `v` and at the midpoint `m` of `v` and the base point
`v₀` of coercivity. -/
theorem tendsto_sub_of_coercive_potential (hJc : ConvexOn ℝ univ J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0)
    (hco : IsCoerciveOp univ A) (f : StrongDual ℝ X) :
    Tendsto (fun v => J v - f v) (Bornology.cobounded X ⊓ 𝓟 univ) atTop := by
  obtain ⟨v₀, -, hv₀⟩ := hco
  rw [principal_univ, inf_top_eq] at hv₀ ⊢
  set L : ℝ := ‖A v₀ - f‖ with hL
  set m : X → X := fun v => (1 / 2 : ℝ) • (v₀ + v) with hm
  have hnorm : Tendsto (fun v => ‖m v‖) (Bornology.cobounded X) atTop := by
    refine tendsto_atTop_mono (fun v => ?_)
      (((tendsto_norm_cobounded_atTop (E := X)).atTop_add
        (tendsto_const_nhds (x := -‖v₀‖))).const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
    have h1 : ‖v‖ ≤ ‖v₀ + v‖ + ‖v₀‖ := by
      calc ‖v‖ = ‖(v₀ + v) - v₀‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖v₀ + v‖ + ‖v₀‖ := norm_sub_le _ _
    have h2 : ‖m v‖ = (1 / 2) * ‖v₀ + v‖ := by
      rw [hm, norm_smul]; simp
    rw [h2]; linarith
  have hmco : Tendsto m (Bornology.cobounded X) (Bornology.cobounded X) :=
    tendsto_norm_atTop_iff_cobounded.mp hnorm
  have hq := hv₀.comp hmco
  have hq' : ∀ᶠ v in Bornology.cobounded X,
      (2 * L + 1) ≤ (A (m v) - A v₀) (m v - v₀) / ‖m v‖ :=
    hq.eventually (eventually_ge_atTop _)
  refine tendsto_atTop.mpr fun b => ?_
  have hbd := hnorm.eventually (eventually_ge_atTop (max 1 (b - J v₀ + f v₀ + 2 * L * ‖v₀‖)))
  filter_upwards [hq', hbd] with v hv hvn
  have hpos : 0 < ‖m v‖ := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hvn)
  have hQ : (2 * L + 1) * ‖m v‖ ≤ (A (m v) - A v₀) (m v - v₀) := by
    rwa [le_div_iff₀ hpos] at hv
  have g1 := gradient_inequality_of_convex_gateaux hJc hJ v₀ (m v)
  have g2 := gradient_inequality_of_convex_gateaux hJc hJ (m v) v
  have hvm : v - m v = m v - v₀ := by
    simp only [hm]; module
  have hv2 : v = v₀ + (2 : ℝ) • (m v - v₀) := by
    simp only [hm]; module
  rw [hvm] at g2
  have hfv : f v = f v₀ + 2 * f (m v - v₀) := by
    conv_lhs => rw [hv2]
    simp [map_add, map_smul]
  have hlin : |(A v₀ - f) (m v - v₀)| ≤ L * ‖m v - v₀‖ := by
    rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
  have hd : ‖m v - v₀‖ ≤ ‖m v‖ + ‖v₀‖ := norm_sub_le _ _
  have hL0 : 0 ≤ L := norm_nonneg _
  have hsub : (A (m v) - A v₀) (m v - v₀) = A (m v) (m v - v₀) - A v₀ (m v - v₀) := by
    simp
  have hsub2 : (A v₀ - f) (m v - v₀) = A v₀ (m v - v₀) - f (m v - v₀) := by simp
  have hle : -(L * ‖m v - v₀‖) ≤ (A v₀ - f) (m v - v₀) := by
    have := neg_abs_le ((A v₀ - f) (m v - v₀)); linarith
  have hLd : L * ‖m v - v₀‖ ≤ L * (‖m v‖ + ‖v₀‖) := mul_le_mul_of_nonneg_left hd hL0
  have hmax : b - J v₀ + f v₀ + 2 * L * ‖v₀‖ ≤ ‖m v‖ := (le_max_right _ _).trans hvn
  nlinarith [hQ, g1, g2, hle, hLd, hmax, hfv, hsub, hsub2]

/-- **Surjectivity of a coercive potential monotone operator.** Let `X` be reflexive, `J` convex
and lower semicontinuous with Gateaux derivative `A`, and `A` coercive. Then `A` is onto the dual.
The proof minimises `J - f` by the direct method, whose minimiser satisfies the variational
inequality of `A - f` on the whole space, which forces `A u = f` (the direct method
is Brezis, Corollary 3.23, p. 71). -/
theorem exists_eq_of_potential (hX : Analysis.IsReflexive X)
    (hJc : ConvexOn ℝ univ J) (hJl : LowerSemicontinuous J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0)
    (hco : IsCoerciveOp univ A) (f : StrongDual ℝ X) : ∃ u, A u = f := by
  have hconv : ConvexOn ℝ univ (fun v => J v - f v) := by
    have := hJc.add (LinearMap.convexOn (-f.toLinearMap) convex_univ)
    convert this using 1
  have hlsc : LowerSemicontinuous (fun v => J v - f v) :=
    hJl.add f.continuous.neg.lowerSemicontinuous
  obtain ⟨u, -, hu⟩ := exists_isMinOn_of_convex hX isClosed_univ univ_nonempty hconv
    (hlsc.lowerSemicontinuousOn _) (tendsto_sub_of_coercive_potential hJc hJ hco f)
  have hJ' : ∀ u v, HasDerivAt (fun t : ℝ => (fun x => J x - f x) (u + t • v))
      ((A u - f) v) 0 := by
    intro u v
    have h2 : HasDerivAt (fun t : ℝ => f (u + t • v)) (f v) 0 := by
      have e : (fun t : ℝ => f (u + t • v)) = fun t => f u + t * f v := by
        ext t; simp
      rw [e]
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (f v)).const_add (f u)
    exact (hJ u v).sub h2
  have hvi := variationalInequality_of_isMinOn (A := fun u => A u - f) hJ' convex_univ
    (mem_univ u) hu
  refine ⟨u, ?_⟩
  ext w
  have h1 := hvi (u + w) (mem_univ _)
  have h2 := hvi (u - w) (mem_univ _)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, map_neg, sub_apply] at h1 h2
  linarith

/-- **Uniqueness for a coercive potential operator.** Under the hypotheses of
`exists_eq_of_potential`, a strictly monotone `A` has exactly one `u` with `A u = f`. -/
theorem existsUnique_eq_of_potential (hX : Analysis.IsReflexive X)
    (hJc : ConvexOn ℝ univ J) (hJl : LowerSemicontinuous J)
    (hJ : ∀ u v, HasDerivAt (fun t : ℝ => J (u + t • v)) (A u v) 0)
    (hco : IsCoerciveOp univ A) (hsm : IsStrictlyMonotoneOp univ A) (f : StrongDual ℝ X) :
    ∃! u, A u = f := by
  obtain ⟨u, hu⟩ := exists_eq_of_potential hX hJc hJl hJ hco f
  refine ⟨u, hu, fun w hw => ?_⟩
  by_contra hne
  have h := hsm w trivial u trivial hne
  rw [hw, hu, sub_self] at h
  simp at h

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Symmetric Lax–Milgram from a potential.** For a bounded, symmetric and coercive bilinear
form `B` on a real Hilbert space, `J u = B u u / 2` is a convex potential of `u ↦ B u`, so
`existsUnique_eq_of_potential` gives the unique solution of `B u v = f v` for all `v`. This agrees
with `EllipticPdes.lax_milgram` (Brezis, Corollary 5.8, p. 140), which drops the symmetry. -/
theorem laxMilgram_symm_of_potential {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B)
    (hsymm : ∀ u v : H, B u v = B v u) (f : H →L[ℝ] ℝ) :
    ∃! u : H, ∀ v : H, B u v = f v := by
  obtain ⟨C, hC, hcoer⟩ := hB
  have hnn : ∀ u, 0 ≤ B u u := fun u =>
    (mul_nonneg (mul_nonneg hC.le (norm_nonneg u)) (norm_nonneg u)).trans (hcoer u)
  have hconv : ConvexOn ℝ univ (fun u : H => B u u / 2) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have hxy := hnn (x - y)
    simp only [map_sub, sub_apply] at hxy
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_nonneg (mul_nonneg ha hb) hxy, hsymm x y]
  have hlsc : LowerSemicontinuous (fun u : H => B u u / 2) :=
    (((B.continuous₂.comp (continuous_id.prodMk continuous_id)).div_const 2)).lowerSemicontinuous
  have hder : ∀ u v : H, HasDerivAt (fun t : ℝ => B (u + t • v) (u + t • v) / 2) (B u v) 0 := by
    intro u v
    have e : (fun t : ℝ => B (u + t • v) (u + t • v) / 2) =
        fun t => B u u / 2 + t * B u v + t * t * (B v v / 2) := by
      ext t
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [hsymm v u]; ring
    rw [e]
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (B u v)).const_add (B u u / 2)
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (B v v / 2)
    have h3 := h1.add h2
    simp only [Pi.add_def] at h3
    simpa using h3
  have hco : IsCoerciveOp univ (fun u : H => B u) := by
    refine ⟨0, mem_univ _, ?_⟩
    rw [principal_univ, inf_top_eq]
    refine tendsto_atTop_mono' _ ?_ (tendsto_norm_cobounded_atTop.const_mul_atTop hC)
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with v hv
    simp only [map_zero, sub_zero]
    rw [le_div_iff₀ hv]
    nlinarith [hcoer v]
  have hsm : IsStrictlyMonotoneOp univ (fun u : H => B u) := by
    intro u _ v _ huv
    have h : (B u - B v) (u - v) = B (u - v) (u - v) := by simp [map_sub]
    have hpos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
    change 0 < (B u - B v) (u - v)
    rw [h]
    exact lt_of_lt_of_le (by positivity) (hcoer _)
  obtain ⟨u, hu, huniq⟩ := existsUnique_eq_of_potential Analysis.isReflexive_of_hilbert hconv
    hlsc hder hco hsm f
  exact ⟨u, fun v => by simpa using congrArg (fun g : H →L[ℝ] ℝ => g v) hu,
    fun w hw => huniq w (ContinuousLinearMap.ext hw)⟩

end Hilbert

end EllipticPdes
