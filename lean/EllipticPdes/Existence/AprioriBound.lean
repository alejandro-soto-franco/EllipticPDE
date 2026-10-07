/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.ClassicalMaximum

/-!
# A priori bound from the maximum principle

For a subsolution of `L u = f` on a bounded open set lying in a slab of width `D` in a
direction `e`, with `c ≥ 0`, the supremum of `u` is bounded by the supremum of its
positive part over the boundary plus `(e^{(B/θ + 1) D} - 1)` times the bound on `f` over `θ`.
The comparison function is `sup u⁺ + (F/θ)(e^{αD} - e^{α (⟪e, x⟫ - m)})` at `α = B/θ + 1`,
whose image under `L` is at least `F`, so the comparison principle applies. A solution is
bounded in absolute value by the same expression with the boundary supremum of `|u|`.

## Main declarations

* `EllipticPdes.Classical.apriori_bound_sub`: the bound for a subsolution.
* `EllipticPdes.Classical.apriori_bound_abs`: the bound for a solution.

## References

Y. Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem XI.5.1
(p. 103); D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Theorem 3.7 (p. 36).
-/

@[expose] public section

open Set Filter Topology Metric InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Classical

/-- **Principal part of the slab comparison function.** If `θ ≤ a₀`, `b₀ ≤ B` and
`α = B / θ + 1` with `B ≥ 0`, then `θ ≤ (a₀ α² - b₀ α) w` whenever `1 ≤ w`. -/
theorem le_slab_principal {θ B α a₀ b₀ w : ℝ} (hθ : 0 < θ) (hB : 0 ≤ B) (hα : α = B / θ + 1)
    (ha : θ ≤ a₀) (hb : b₀ ≤ B) (hw : 1 ≤ w) : θ ≤ (a₀ * α ^ 2 - b₀ * α) * w := by
  have hα1 : 1 ≤ α := by
    have : 0 ≤ B / θ := div_nonneg hB hθ.le
    linarith
  have hθα : θ * α = B + θ := by
    rw [hα]
    field_simp
  have h3 : θ * α ≤ a₀ * α ^ 2 - b₀ * α := by
    have e1 : θ * α ^ 2 ≤ a₀ * α ^ 2 := mul_le_mul_of_nonneg_right ha (sq_nonneg α)
    have e2 : b₀ * α ≤ B * α := mul_le_mul_of_nonneg_right hb (by linarith)
    have e3 : θ * α ^ 2 - B * α = θ * α := by linear_combination α * hθα
    linarith
  have h5 : 0 ≤ a₀ * α ^ 2 - b₀ * α := by nlinarith
  calc θ ≤ a₀ * α ^ 2 - b₀ * α := by nlinarith
    _ = (a₀ * α ^ 2 - b₀ * α) * 1 := (mul_one _).symm
    _ ≤ (a₀ * α ^ 2 - b₀ * α) * w := mul_le_mul_of_nonneg_left hw h5

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {A : E → E →L[ℝ] E} {b : E → E} {c : E → ℝ} {U : Set E} {θ B : ℝ}

omit [FiniteDimensional ℝ E] in
/-- A slab bound on a set extends to its closure. -/
theorem slab_closure {e : E} {m D : ℝ} (hslab : ∀ x ∈ U, m ≤ ⟪e, x⟫ ∧ ⟪e, x⟫ ≤ m + D) :
    ∀ x ∈ closure U, m ≤ ⟪e, x⟫ ∧ ⟪e, x⟫ ≤ m + D := by
  have hcont : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  have hcl : IsClosed {x : E | m ≤ ⟪e, x⟫ ∧ ⟪e, x⟫ ≤ m + D} :=
    (isClosed_le continuous_const hcont).inter (isClosed_le hcont continuous_const)
  exact fun x hx => (hcl.closure_subset_iff.mpr fun y hy => hslab y hy) hx

namespace nondivOperator

/-- **Maximum-principle bound for a subsolution** (Guo Theorem XI.5.1(i), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u ≤ f` and `f ≤ F` is bounded by the maximum of its positive part over the boundary
plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_sub (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hB0 : 0 ≤ B)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {m D : ℝ}
    (hslab : ∀ x ∈ U, m ≤ ⟪e, x⟫ ∧ ⟪e, x⟫ ≤ m + D) {u f : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOperator A b c u x ≤ f x)
    {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ x ∈ U, f x ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      u x ≤ max (u y) 0 + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  obtain ⟨x₁, hx₁⟩ := hUne
  have hθ := hA.pos
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty ⟨x₁, hx₁⟩)
    (huc.mono frontier_subset_closure)
  refine ⟨y, hyfr, ?_⟩
  set K : ℝ := max (u y) 0 with hK
  set α : ℝ := B / θ + 1 with hα
  have hα0 : 0 < α := by positivity
  have hF' : 0 ≤ F / θ := div_nonneg hF0 hθ.le
  set ε : ℝ := -(F / θ) * Real.exp (-α * m) with hε
  set c₀ : ℝ := K + F / θ * Real.exp (α * D) with hc₀
  set v : E → ℝ := fun x => c₀ + ε * expInner α e x with hv
  have hvx : ∀ x, v x = K + F / θ * (Real.exp (α * D) - Real.exp (α * (⟪e, x⟫ - m))) := by
    intro x
    simp only [hv, hc₀, hε, expInner]
    rw [show α * (⟪e, x⟫ - m) = -α * m + α * ⟪e, x⟫ by ring, Real.exp_add]
    ring
  have hexp : ContDiff ℝ 2 (expInner α e) := contDiff_expInner _ _
  have hvC : ContDiffOn ℝ 2 v U := contDiffOn_const.add (contDiffOn_const.mul hexp.contDiffOn)
  have hvc : ContinuousOn v (closure U) :=
    continuousOn_const.add (continuousOn_const.mul hexp.continuous.continuousOn)
  -- `v` is nonnegative and at most `K + (e^{αD} - 1) F/θ` on the closure
  have hvbd : ∀ x ∈ closure U, 0 ≤ v x ∧ v x ≤ K + (Real.exp (α * D) - 1) * (F / θ) := by
    intro x hx
    obtain ⟨h1, h2⟩ := slab_closure hslab x hx
    rw [hvx]
    have e1 : 1 ≤ Real.exp (α * (⟪e, x⟫ - m)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hα0.le (by linarith))
    have e2 : Real.exp (α * (⟪e, x⟫ - m)) ≤ Real.exp (α * D) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hα0.le)
    constructor
    · nlinarith [mul_nonneg hF' (sub_nonneg.mpr e2), le_max_right (u y) 0]
    · nlinarith [mul_nonneg hF' (sub_nonneg.mpr e1)]
  -- `L u ≤ L v` on the set
  have hL : ∀ x ∈ U, nondivOperator A b c u x ≤ nondivOperator A b c v x := by
    intro x hx
    obtain ⟨h1, _⟩ := hslab x hx
    have hexp2 := hexp.contDiffAt (x := x)
    rw [hv, nondivOperator_add_smul A b c contDiffAt_const hexp2, nondivOperator_const,
      nondivOperator_expInner]
    have hw : 1 ≤ Real.exp (-α * m) * expInner α e x := by
      simp only [expInner]
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hprin : θ ≤ (⟪e, A x e⟫ * α ^ 2 - ⟪e, b x⟫ * α)
        * (Real.exp (-α * m) * expInner α e x) :=
      le_slab_principal hθ hB0 hα (by simpa [real_inner_comm] using hA.le_inner_self hx he)
        (by simpa [real_inner_comm] using hb x hx) hw
    have hcv : 0 ≤ c x * v x := mul_nonneg (hc x hx) (hvbd x (subset_closure hx)).1
    have hvx' := hvx x
    simp only [hv] at hvx' hcv
    have key : c x * c₀ + ε * ((-(α ^ 2 * ⟪e, A x e⟫) + α * ⟪e, b x⟫ + c x) * expInner α e x)
        = F / θ * ((⟪e, A x e⟫ * α ^ 2 - ⟪e, b x⟫ * α)
            * (Real.exp (-α * m) * expInner α e x)) + c x * (c₀ + ε * expInner α e x) := by
      simp only [hε]
      ring
    rw [key]
    calc nondivOperator A b c u x ≤ f x := hsub x hx
      _ ≤ F := hF x hx
      _ = F / θ * θ := (div_mul_cancel₀ F hθ.ne').symm
      _ ≤ F / θ * ((⟪e, A x e⟫ * α ^ 2 - ⟪e, b x⟫ * α) * (Real.exp (-α * m) * expInner α e x))
          + c x * (c₀ + ε * expInner α e x) := by
        linarith [mul_le_mul_of_nonneg_left hprin hF']
  -- `u ≤ v` on the frontier
  have hbd : ∀ x ∈ frontier U, u x ≤ v x := by
    intro x hx
    obtain ⟨_, hx2⟩ := slab_closure hslab x (frontier_subset_closure hx)
    have h4 : 0 ≤ F / θ * (Real.exp (α * D) - Real.exp (α * (⟪e, x⟫ - m))) :=
      mul_nonneg hF' (sub_nonneg.mpr (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (by linarith) hα0.le)))
    rw [hvx]
    have h1 : u x ≤ u y := hymax hx
    linarith [le_max_left (u y) 0]
  intro x hx
  have := comparison_principle hU hUb ⟨x₁, hx₁⟩ hA he hb hc hu hvC huc hvc hL hbd x hx
  linarith [(hvbd x hx).2]

/-- **Maximum-principle bound for a solution** (Guo Theorem XI.5.1(ii), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u = f` and `|f| ≤ F` is bounded in absolute value by the maximum of `|u|` over the
boundary plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_abs (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hA : IsUniformlyElliptic A U θ) {e : E} (he : ‖e‖ = 1) (hB0 : 0 ≤ B)
    (hb : ∀ x ∈ U, ⟪b x, e⟫ ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x) {m D : ℝ}
    (hslab : ∀ x ∈ U, m ≤ ⟪e, x⟫ ∧ ⟪e, x⟫ ≤ m + D) {u f : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOperator A b c u x = f x)
    {F : ℝ} (hF : ∀ x ∈ U, |f x| ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      |u x| ≤ |u y| + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  have : Nontrivial E := ⟨⟨e, 0, fun h => by simp [h] at he⟩⟩
  obtain ⟨x₁, hx₁⟩ := hUne
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF x₁ hx₁)
  have hfr : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨y, hyfr, hymax⟩ := hfr.exists_isMaxOn (hUb.frontier_nonempty ⟨x₁, hx₁⟩)
    ((huc.mono frontier_subset_closure).abs)
  refine ⟨y, hyfr, fun x hx => ?_⟩
  obtain ⟨y₁, hy₁, h₁⟩ := apriori_bound_sub hU hUb ⟨x₁, hx₁⟩ hA he hB0 hb hc hslab hu huc
    (f := f) (fun x hx => (hsol x hx).le) hF0 (fun x hx => (le_abs_self _).trans (hF x hx))
  obtain ⟨y₂, hy₂, h₂⟩ := apriori_bound_sub hU hUb ⟨x₁, hx₁⟩ hA he hB0 hb hc hslab hu.neg huc.neg
    (f := fun y => -f y) (fun x hx => by
      rw [nondivOperator_neg A b c (hu.contDiffAt (hU.mem_nhds hx)), hsol x hx])
    hF0 (fun x hx => (neg_le_abs _).trans (hF x hx))
  have m₁ : max (u y₁) 0 ≤ |u y₁| := max_le (le_abs_self _) (abs_nonneg _)
  have m₂ : max (-u y₂) 0 ≤ |u y₂| := max_le (neg_le_abs _) (abs_nonneg _)
  have e₁ := h₁ x hx
  have e₂ := h₂ x hx
  rw [abs_le]
  have n₁ : |u y₁| ≤ |u y| := hymax hy₁
  have n₂ : |u y₂| ≤ |u y| := hymax hy₂
  constructor <;> linarith

end nondivOperator

end General

/-! ### Euclidean space with a coefficient matrix -/

variable {d : ℕ}

/-- **Maximum-principle bound for a subsolution** (Guo Theorem XI.5.1(i), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u ≤ f` and `f ≤ F` is bounded by the maximum of its positive part over the boundary
plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_sub (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {i₀ : Fin d} {m D : ℝ} (hslab : ∀ x ∈ U, m ≤ x i₀ ∧ x i₀ ≤ m + D)
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsub : ∀ x ∈ U, nondivOp a b c u x ≤ f x)
    {F : ℝ} (hF0 : 0 ≤ F) (hF : ∀ x ∈ U, f x ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      u x ≤ max (u y) 0 + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  have _ := hd
  have hA := isUniformlyElliptic_matrixCLM hθ hsymm hell
  have he : ‖(EuclideanSpace.single i₀ (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
  have hb' : ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)),
      EuclideanSpace.single i₀ (1 : ℝ)⟫ ≤ B := fun x hx => by
    rw [EuclideanSpace.inner_single_right]
    simpa using (abs_le.mp (hb x hx i₀)).2
  have hB0 : 0 ≤ B := by
    obtain ⟨x₁, hx₁⟩ := hUne
    exact (abs_nonneg _).trans (hb x₁ hx₁ i₀)
  have hslab' : ∀ x ∈ U, m ≤ ⟪EuclideanSpace.single i₀ (1 : ℝ), x⟫ ∧
      ⟪EuclideanSpace.single i₀ (1 : ℝ), x⟫ ≤ m + D := fun x hx => by
    simpa [EuclideanSpace.inner_single_left] using hslab x hx
  exact nondivOperator.apriori_bound_sub hU hUb hUne hA he hB0 hb' hc hslab' hu huc
    (fun x hx => by rw [← nondivOp_eq_of_contDiffOn hU hu hx]; exact hsub x hx) hF0 hF

/-- **Maximum-principle bound for a solution** (Guo Theorem XI.5.1(ii), Gilbarg and Trudinger
Theorem 3.7). On a bounded open set inside the slab `m ≤ x_{i₀} ≤ m + D`, with `c ≥ 0`, a function
with `L u = f` and `|f| ≤ F` is bounded in absolute value by the maximum of `|u|` over the
boundary plus `(e^{(B/θ + 1) D} - 1) F/θ`. -/
theorem apriori_bound_abs (hd : 0 < d) {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    {a : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ} {b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ}
    {c : EuclideanSpace ℝ (Fin d) → ℝ}
    {θ B : ℝ} (hθ : 0 < θ) (hsymm : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hell : ∀ x ∈ U, ∀ ξ : Fin d → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j)
    (hb : ∀ x ∈ U, ∀ i, |b x i| ≤ B) (hc : ∀ x ∈ U, 0 ≤ c x)
    {i₀ : Fin d} {m D : ℝ} (hslab : ∀ x ∈ U, m ≤ x i₀ ∧ x i₀ ≤ m + D)
    {u f : EuclideanSpace ℝ (Fin d) → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (huc : ContinuousOn u (closure U)) (hsol : ∀ x ∈ U, nondivOp a b c u x = f x)
    {F : ℝ} (hF : ∀ x ∈ U, |f x| ≤ F) :
    ∃ y ∈ frontier U, ∀ x ∈ closure U,
      |u x| ≤ |u y| + (Real.exp ((B / θ + 1) * D) - 1) * (F / θ) := by
  have _ := hd
  have hA := isUniformlyElliptic_matrixCLM hθ hsymm hell
  have he : ‖(EuclideanSpace.single i₀ (1 : ℝ) : EuclideanSpace ℝ (Fin d))‖ = 1 := by simp
  have hb' : ∀ x ∈ U, ⟪(WithLp.toLp 2 (b x) : EuclideanSpace ℝ (Fin d)),
      EuclideanSpace.single i₀ (1 : ℝ)⟫ ≤ B := fun x hx => by
    rw [EuclideanSpace.inner_single_right]
    simpa using (abs_le.mp (hb x hx i₀)).2
  have hB0 : 0 ≤ B := by
    obtain ⟨x₁, hx₁⟩ := hUne
    exact (abs_nonneg _).trans (hb x₁ hx₁ i₀)
  have hslab' : ∀ x ∈ U, m ≤ ⟪EuclideanSpace.single i₀ (1 : ℝ), x⟫ ∧
      ⟪EuclideanSpace.single i₀ (1 : ℝ), x⟫ ≤ m + D := fun x hx => by
    simpa [EuclideanSpace.inner_single_left] using hslab x hx
  exact nondivOperator.apriori_bound_abs hU hUb hUne hA he hB0 hb' hc hslab' hu huc
    (fun x hx => by rw [← nondivOp_eq_of_contDiffOn hU hu hx]; exact hsol x hx) hF

end EllipticPdes.Classical
