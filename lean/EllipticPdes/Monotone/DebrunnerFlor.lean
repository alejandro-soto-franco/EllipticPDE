/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Monotone.Basic
public import EllipticPdes.Monotone.DebrunnerFlorFinite
public import EllipticPdes.Monotone.ReflexiveCompact

/-!
# Weak variational inequality for monotone coercive operators

Ferreira–Gomes–Üçer (`ferreira-2025-sol-mea-gam`, Theorem 2.16, p. 11) state that a monotone
coercive operator `A : K → X*` on a nonempty convex subset `K` of a reflexive Banach space has a
point `u ∈ closure K` with `0 ≤ ⟨A v, v - u⟩` for every `v ∈ K`. The closure cannot be dropped
for a non-closed convex set: take `X = ℝ`, `K = (0, 1]` and `A v = id`.
`EllipticPdes.weakVI_Ioc_counterexample` proves this. The general theorem below is the printed
statement, and the closed case gives `u ∈ K`, the form Remark 2.17 (p. 12) starts from.

The proof follows the paper. Coercivity bounds the solutions of the finite-dimensional problems
of `EllipticPdes.Monotone.DebrunnerFlorFinite` by a radius `r` that does not depend on the finite
family, and weak compactness of `closedBall 0 r ∩ closure K` lets the finite intersection
property pass to all of `K`.

## Main declarations

* `EllipticPdes.IsCoerciveOp.of_isBounded`: on a bounded set coercivity is automatic.
* `EllipticPdes.exists_weakVI_closure`: the weak variational inequality with `u ∈ closure K`.
* `EllipticPdes.exists_weakVI`: Theorem 2.16 for closed `K`.
* `EllipticPdes.exists_weakVI_of_isBounded`: the bounded case, with no coercivity hypothesis.
* `EllipticPdes.weakVI_Ioc_counterexample`: the counterexample for `K = (0, 1]`.
-/

@[expose] public section

namespace EllipticPdes

open Set Filter Topology Metric

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- On a bounded set, coercivity is vacuous because `cobounded X ⊓ 𝓟 K` is trivial. -/
theorem IsCoerciveOp.of_isBounded {K : Set X} (hK : Bornology.IsBounded K) (hne : K.Nonempty)
    (A : X → StrongDual ℝ X) : IsCoerciveOp K A := by
  obtain ⟨v₀, hv₀⟩ := hne
  refine ⟨v₀, hv₀, ?_⟩
  have h : Bornology.cobounded X ⊓ 𝓟 K = ⊥ := by
    rw [← disjoint_iff, Filter.disjoint_principal_right]
    exact hK
  rw [h]
  exact tendsto_bot

/-- A norm-closed half-space `{u | 0 ≤ ⟨A v, v - u⟩}` is convex. -/
private lemma convex_halfSpace (φ : StrongDual ℝ X) (v : X) :
    Convex ℝ {u : X | 0 ≤ φ (v - u)} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at *
  have : v - (a • x + b • y) = a • (v - x) + b • (v - y) + (1 - (a + b)) • v := by module
  rw [hab, sub_self, zero_smul, add_zero] at this
  rw [this, map_add, map_smul, map_smul]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

private lemma isClosed_halfSpace (φ : StrongDual ℝ X) (v : X) :
    IsClosed {u : X | 0 ≤ φ (v - u)} :=
  isClosed_le continuous_const (φ.continuous.comp (continuous_const.sub continuous_id))

/-- A radius bound from coercivity: along `K`, a solution `w` of `⟨A w, w - v₀⟩ ≤ 0` has
`‖w‖ ≤ R`. -/
private lemma exists_radius {K : Set X} {A : X → StrongDual ℝ X} {v₀ : X}
    (h : Tendsto (fun v => (A v - A v₀) (v - v₀) / ‖v‖) (Bornology.cobounded X ⊓ 𝓟 K) atTop) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ w ∈ K, A w (w - v₀) ≤ 0 → ‖w‖ ≤ R := by
  have h1 := h.eventually (eventually_ge_atTop (‖A v₀‖ + 1))
  rw [Filter.eventually_inf_principal,
    (Metric.hasBasis_cobounded_compl_closedBall (0 : X)).eventually_iff] at h1
  obtain ⟨r, -, hr⟩ := h1
  refine ⟨max (max r 1) (‖A v₀‖ * ‖v₀‖), le_trans (le_max_right _ _) (le_max_left _ _), ?_⟩
  intro w hw hAw
  by_contra hlt
  push Not at hlt
  have hrw : r < ‖w‖ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hlt
  have hw1 : 1 < ‖w‖ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hlt
  have hq := hr (by simpa [mem_compl_iff, mem_closedBall, dist_zero_right] using hrw) hw
  have hpos : 0 < ‖w‖ := by linarith
  rw [le_div_iff₀ hpos] at hq
  have hb : -(A v₀) (w - v₀) ≤ ‖A v₀‖ * (‖w‖ + ‖v₀‖) :=
    (neg_le_abs _).trans <| (A v₀).le_opNorm _ |>.trans
      (by gcongr; exact norm_sub_le _ _)
  have hsub : (A w - A v₀) (w - v₀) = A w (w - v₀) - A v₀ (w - v₀) := by simp
  have hlt2 : ‖A v₀‖ * ‖v₀‖ < ‖w‖ := lt_of_le_of_lt (le_max_right _ _) hlt
  nlinarith [norm_nonneg (A v₀), norm_nonneg v₀]

/-- **Ferreira–Gomes–Üçer, Theorem 2.16, general form** (`ferreira-2025-sol-mea-gam`, p. 11).
For a monotone coercive operator `A` on a convex subset `K` of a reflexive Banach space there
is a point `u` of the closure of `K` with `0 ≤ ⟨A v, v - u⟩` for every `v ∈ K`. The conclusion
`u ∈ K` needs `K` closed (`exists_weakVI`). Coercivity names a point of
`K`. Hence `K` is nonempty without a separate hypothesis. -/
theorem exists_weakVI_closure (hX : Analysis.IsReflexive X) {K : Set X}
    (hK : Convex ℝ K) {A : X → StrongDual ℝ X} (hA : IsMonotoneOp K A)
    (hco : IsCoerciveOp K A) : ∃ u ∈ closure K, ∀ v ∈ K, 0 ≤ A v (v - u) := by
  obtain ⟨v₀, hv₀, hT⟩ := hco
  obtain ⟨R, -, hR⟩ := exists_radius hT
  set r : ℝ := 2 * R + ‖v₀‖ with hr
  -- finite subfamilies have solutions in the ball
  have hfin : ∀ F : Finset K, ∃ u : X, u ∈ closedBall (0 : X) r ∧ u ∈ closure K ∧
      ∀ v ∈ F, 0 ≤ A (v : X) ((v : X) - u) := by
    intro F
    classical
    set S : Finset X := insert v₀ (F.image Subtype.val) with hS
    have hSne : S.Nonempty := ⟨v₀, Finset.mem_insert_self _ _⟩
    have hSK : (↑S : Set X) ⊆ K := by
      intro x hx
      simp only [hS, Finset.coe_insert, Finset.coe_image, mem_insert_iff, mem_image,
        Finset.mem_coe] at hx
      rcases hx with rfl | ⟨y, -, rfl⟩
      · exact hv₀
      · exact y.2
    have hhull : convexHull ℝ (↑S : Set X) ⊆ K := convexHull_min hSK hK
    obtain ⟨u, huC, hu⟩ := exists_minty_convexHull_finset hSne
      (fun a ha b hb => hA a (hhull ha) b (hhull hb))
    have huK : u ∈ K := hhull huC
    have hv₀S : v₀ ∈ convexHull ℝ (↑S : Set X) :=
      subset_convexHull ℝ _ (by simp [hS])
    have hwC : (1 / 2 : ℝ) • (u + v₀) ∈ convexHull ℝ (↑S : Set X) := by
      have := (convex_convexHull ℝ (↑S : Set X)) huC hv₀S (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      simpa [smul_add] using this
    set w : X := (1 / 2 : ℝ) • (u + v₀) with hw
    have h1 := hu w hwC
    have hwu : w - u = -(w - v₀) := by rw [hw]; module
    rw [hwu, map_neg] at h1
    have hwR := hR w (hhull hwC) (by linarith)
    have hu2 : u = (2 : ℝ) • w - v₀ := by rw [hw]; module
    refine ⟨u, ?_, subset_closure huK, fun v hv => hu _ (subset_convexHull ℝ _ ?_)⟩
    · rw [mem_closedBall, dist_zero_right, hu2]
      calc ‖(2 : ℝ) • w - v₀‖ ≤ ‖(2 : ℝ) • w‖ + ‖v₀‖ := norm_sub_le _ _
        _ = 2 * ‖w‖ + ‖v₀‖ := by rw [norm_smul]; norm_num
        _ ≤ r := by rw [hr]; linarith
    · simp [hS, hv]
  -- weak compactness and the finite intersection property
  have hconvB : Convex ℝ (closedBall (0 : X) r ∩ closure K) :=
    (convex_closedBall _ _).inter hK.closure
  have hcpt : IsCompact (toWeakSpace ℝ X '' (closedBall (0 : X) r ∩ closure K)) :=
    isCompact_toWeakSpace_of_bounded_convex_closed hX hconvB
      (isClosed_closedBall.inter isClosed_closure)
      ((isBounded_closedBall).subset inter_subset_left)
  have key := hcpt.inter_iInter_nonempty
    (fun v : K => toWeakSpace ℝ X '' {u : X | 0 ≤ A (v : X) ((v : X) - u)})
    (fun v => isClosed_toWeakSpace_of_convex (convex_halfSpace _ _) (isClosed_halfSpace _ _))
    (by
      intro F
      obtain ⟨u, hub, huc, hu⟩ := hfin F
      refine ⟨toWeakSpace ℝ X u, ⟨u, ⟨hub, huc⟩, rfl⟩, ?_⟩
      simp only [mem_iInter]
      intro v hv
      exact ⟨u, hu v hv, rfl⟩)
  obtain ⟨p, ⟨u, ⟨-, huc⟩, rfl⟩, hp⟩ := key
  refine ⟨u, huc, fun v hv => ?_⟩
  have := mem_iInter.mp hp ⟨v, hv⟩
  obtain ⟨y, hy, hyu⟩ := this
  rw [← (toWeakSpace ℝ X).injective hyu]
  exact hy

/-- **Ferreira–Gomes–Üçer, Theorem 2.16** (`ferreira-2025-sol-mea-gam`, p. 11) for a closed
convex set `K`: a monotone coercive operator has a point `u ∈ K` with
`0 ≤ ⟨A v, v - u⟩` for every `v ∈ K`. -/
theorem exists_weakVI (hX : Analysis.IsReflexive X) {K : Set X}
    (hK : Convex ℝ K) (hc : IsClosed K) {A : X → StrongDual ℝ X}
    (hA : IsMonotoneOp K A) (hco : IsCoerciveOp K A) : ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A v (v - u) := by
  obtain ⟨u, hu, h⟩ := exists_weakVI_closure hX hK hA hco
  exact ⟨u, hc.closure_eq ▸ hu, h⟩

/-- **Debrunner–Flor theorem.** A monotone operator on a bounded closed convex nonempty subset of
a reflexive Banach space satisfies the weak variational inequality, with no coercivity hypothesis
(compare `ferreira-2025-sol-mea-gam`, Theorem 2.16, p. 11). -/
theorem exists_weakVI_of_isBounded (hX : Analysis.IsReflexive X) {K : Set X}
    (hK : Convex ℝ K) (hc : IsClosed K) (hb : Bornology.IsBounded K) (hne : K.Nonempty)
    {A : X → StrongDual ℝ X} (hA : IsMonotoneOp K A) : ∃ u ∈ K, ∀ v ∈ K, 0 ≤ A v (v - u) :=
  exists_weakVI hX hK hc hA (IsCoerciveOp.of_isBounded hb hne A)

/-- **Counterexample to the conclusion `u ∈ K` of Theorem 2.16 for a convex set.** On `X = ℝ`
with `K = (0, 1]` and `A v = id`, the set `K` is convex and nonempty and `A` is monotone and
coercive, yet no `u ∈ K` satisfies `0 ≤ ⟨A v, v - u⟩` for all `v ∈ K`. Theorem 2.16 of
`ferreira-2025-sol-mea-gam` (p. 11) concludes `u ∈ closure K`. This example shows that the
closure is needed, and `u ∈ K` needs `K` closed. -/
theorem weakVI_Ioc_counterexample :
    let A : ℝ → StrongDual ℝ ℝ := fun _ => ContinuousLinearMap.id ℝ ℝ
    Convex ℝ (Ioc (0 : ℝ) 1) ∧ (Ioc (0 : ℝ) 1).Nonempty ∧ IsMonotoneOp (Ioc (0 : ℝ) 1) A ∧
      IsCoerciveOp (Ioc (0 : ℝ) 1) A ∧
      ¬ ∃ u ∈ Ioc (0 : ℝ) 1, ∀ v ∈ Ioc (0 : ℝ) 1, 0 ≤ A v (v - u) := by
  intro A
  have hne : (Ioc (0 : ℝ) 1).Nonempty := ⟨1, by norm_num⟩
  refine ⟨convex_Ioc 0 1, hne, ?_, IsCoerciveOp.of_isBounded (Metric.isBounded_Ioc 0 1) hne A, ?_⟩
  · intro u _ v _
    simp [A]
  · rintro ⟨u, hu, h⟩
    have := h (u / 2) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    simp [A] at this
    linarith [hu.1]

end EllipticPdes
