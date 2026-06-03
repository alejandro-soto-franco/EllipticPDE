import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# One-dimensional Poincaré inequality (dependency-chain step 1)

For a continuously differentiable `u` on a compact interval `[a, b]` that
vanishes at the left endpoint, the `L²` norm of `u` is controlled by the `L²`
norm of its derivative:
`∫ x in a..b, (u x)^2 ≤ (b - a)^2 / 2 * ∫ x in a..b, (u' x)^2`.

The proof has three steps. First, an integral Cauchy-Schwarz bound
(`sq_intervalIntegral_le`) obtained from the nonnegativity of the quadratic
`λ ↦ ∫ (f - λ)^2` together with the discriminant criterion. Second, the
fundamental theorem of calculus writes `u x` as `∫ t in a..x, u' t`, which the
Cauchy-Schwarz bound turns into a pointwise estimate `(u x)^2 ≤ M * (x - a)`
with `M = ∫ t in a..b, (u' t)^2`. Third, integrating that estimate over `[a, b]`
and evaluating `∫ x in a..b, (x - a) = (b - a)^2 / 2` gives the result.

This is the first standalone Mathlib pull request target (M2).
-/

open MeasureTheory intervalIntegral Set

namespace EllipticDirichlet.Poincare

/-- Cauchy-Schwarz for the interval integral: the square of `∫ f g` is at most
the product of `∫ f ^ 2` and `∫ g ^ 2`. Proved from `0 ≤ ∫ (f - λ g) ^ 2`, read
as a nonnegative quadratic in `λ` whose discriminant must therefore be
nonpositive. The continuity bound on the divergence-form bilinear form (the
`L²` estimate `B[u, v] ≤ β ‖u‖ ‖v‖`) rests on this. -/
theorem intervalIntegral_mul_sq_le {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a b)) (hg : ContinuousOn g (uIcc a b)) :
    (∫ t in a..b, f t * g t) ^ 2 ≤ (∫ t in a..b, (f t) ^ 2) * ∫ t in a..b, (g t) ^ 2 := by
  have hf2I : IntervalIntegrable (fun t => (f t) ^ 2) volume a b := (hf.pow 2).intervalIntegrable
  have hg2I : IntervalIntegrable (fun t => (g t) ^ 2) volume a b := (hg.pow 2).intervalIntegrable
  have hfgI : IntervalIntegrable (fun t => f t * g t) volume a b := (hf.mul hg).intervalIntegrable
  -- The quadratic `λ ↦ (∫ g²) λ² - 2 (∫ f g) λ + ∫ f²` is nonnegative.
  have key : ∀ lam : ℝ,
      0 ≤ (∫ t in a..b, (g t) ^ 2) * (lam * lam)
          + (-(2 * ∫ t in a..b, f t * g t)) * lam + ∫ t in a..b, (f t) ^ 2 := by
    intro lam
    have hnn : 0 ≤ ∫ t in a..b, (f t - lam * g t) ^ 2 :=
      integral_nonneg hab (fun t _ => by positivity)
    have hexp : (∫ t in a..b, (f t - lam * g t) ^ 2)
        = (∫ t in a..b, (g t) ^ 2) * (lam * lam)
          + (-(2 * ∫ t in a..b, f t * g t)) * lam + ∫ t in a..b, (f t) ^ 2 := by
      have hrw : (fun t => (f t - lam * g t) ^ 2)
          = (fun t => (f t) ^ 2 - (2 * lam) * (f t * g t) + lam ^ 2 * (g t) ^ 2) := by
        funext t; ring
      rw [hrw,
        integral_add (hf2I.sub (hfgI.const_mul (2 * lam))) (hg2I.const_mul (lam ^ 2)),
        integral_sub hf2I (hfgI.const_mul (2 * lam)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [← hexp]; exact hnn
  have hdisc := discrim_le_zero key
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- Cauchy-Schwarz with one factor constant: on `[a, x]` the square of the
integral of `f` is at most `(x - a)` times the integral of `f ^ 2`. The `g = 1`
case of [`intervalIntegral_mul_sq_le`]. -/
theorem sq_intervalIntegral_le {a x : ℝ} (hax : a ≤ x) {f : ℝ → ℝ}
    (hf : ContinuousOn f (uIcc a x)) :
    (∫ t in a..x, f t) ^ 2 ≤ (x - a) * ∫ t in a..x, (f t) ^ 2 := by
  have h := intervalIntegral_mul_sq_le hax hf (continuousOn_const (c := (1 : ℝ)))
  simp only [mul_one, one_pow] at h
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, mul_comm] at h
  exact h

/-- One-dimensional Poincaré inequality. If `u` has derivative `u'` at every
point of `[a, b]` with `u'` continuous there, and `u a = 0`, then
`∫ x in a..b, (u x)^2 ≤ (b - a)^2 / 2 * ∫ x in a..b, (u' x)^2`. -/
theorem poincare_oneDim {a b : ℝ} (hab : a ≤ b) {u u' : ℝ → ℝ}
    (hderiv : ∀ y ∈ uIcc a b, HasDerivAt u (u' y) y)
    (hu' : ContinuousOn u' (uIcc a b)) (ha : u a = 0) :
    ∫ x in a..b, (u x) ^ 2 ≤ (b - a) ^ 2 / 2 * ∫ x in a..b, (u' x) ^ 2 := by
  set M : ℝ := ∫ x in a..b, (u' x) ^ 2 with hM
  have hu'2 : ContinuousOn (fun t => (u' t) ^ 2) (uIcc a b) := hu'.pow 2
  have hu_cont : ContinuousOn u (uIcc a b) :=
    fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  -- Pointwise estimate from FTC and the Cauchy-Schwarz bound.
  have pointwise : ∀ x ∈ Icc a b, (u x) ^ 2 ≤ M * (x - a) := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have hsub : uIcc a x ⊆ uIcc a b := by
      rw [uIcc_of_le hax, uIcc_of_le hab]; exact Icc_subset_Icc_right hxb
    have hsubxb : uIcc x b ⊆ uIcc a b := by
      rw [uIcc_of_le hxb, uIcc_of_le hab]; exact Icc_subset_Icc_left hax
    -- `u x = ∫ t in a..x, u' t` by the fundamental theorem of calculus.
    have hux : u x = ∫ t in a..x, u' t := by
      rw [integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hsub ht))
        ((hu'.mono hsub).intervalIntegrable), ha, sub_zero]
    have hcs : (∫ t in a..x, u' t) ^ 2 ≤ (x - a) * ∫ t in a..x, (u' t) ^ 2 :=
      sq_intervalIntegral_le hax (hu'.mono hsub)
    -- `∫ t in a..x, (u')² ≤ M` since the integrand is nonnegative.
    have hmono : ∫ t in a..x, (u' t) ^ 2 ≤ M := by
      have hI1 : IntervalIntegrable (fun t => (u' t) ^ 2) volume a x :=
        (hu'2.mono hsub).intervalIntegrable
      have hI2 : IntervalIntegrable (fun t => (u' t) ^ 2) volume x b :=
        (hu'2.mono hsubxb).intervalIntegrable
      have hadj := integral_add_adjacent_intervals hI1 hI2
      have hxbnn : 0 ≤ ∫ t in x..b, (u' t) ^ 2 :=
        integral_nonneg hxb (fun t _ => by positivity)
      rw [hM]; linarith [hadj, hxbnn]
    calc (u x) ^ 2 = (∫ t in a..x, u' t) ^ 2 := by rw [hux]
      _ ≤ (x - a) * ∫ t in a..x, (u' t) ^ 2 := hcs
      _ ≤ (x - a) * M := mul_le_mul_of_nonneg_left hmono (by linarith)
      _ = M * (x - a) := by ring
  -- Integrate the pointwise estimate over `[a, b]`.
  have hfint : IntervalIntegrable (fun x => (u x) ^ 2) volume a b :=
    (hu_cont.pow 2).intervalIntegrable
  have hgint : IntervalIntegrable (fun x => M * (x - a)) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => M * (x - a)).intervalIntegrable a b
  have hmain : ∫ x in a..b, (u x) ^ 2 ≤ ∫ x in a..b, M * (x - a) :=
    integral_mono_on hab hfint hgint pointwise
  -- `∫ x in a..b, (x - a) = (b - a)^2 / 2`.
  have hxa : ∫ x in a..b, (x - a) = (b - a) ^ 2 / 2 := by
    have hd : ∀ y ∈ uIcc a b, HasDerivAt (fun z => (z - a) ^ 2 / 2) (y - a) y := by
      intro y _
      have hg : HasDerivAt (fun z : ℝ => z - a) 1 y := (hasDerivAt_id y).sub_const a
      have h1 : HasDerivAt (fun z => (z - a) ^ 2) (2 * (y - a)) y := by
        -- v4.31: `simpa` rewrites `fun z => (z-a)^2` into the pointwise function
        -- power `(fun z => z-a)^2` (changed simp normal form), breaking the match.
        -- `convert` matches structurally and bridges the instance diamond by defeq;
        -- only the numeric coefficient `↑2 * (y-a)^(2-1) * 1 = 2*(y-a)` remains.
        have h := hg.pow 2
        convert h using 1
        norm_num
      have h2 := HasDerivAt.div_const h1 2
      rw [show y - a = 2 * (y - a) / 2 by ring]; exact h2
    rw [integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun x : ℝ => x - a).intervalIntegrable a b)]
    simp
  calc ∫ x in a..b, (u x) ^ 2 ≤ ∫ x in a..b, M * (x - a) := hmain
    _ = M * ∫ x in a..b, (x - a) := by rw [intervalIntegral.integral_const_mul]
    _ = M * ((b - a) ^ 2 / 2) := by rw [hxa]
    _ = (b - a) ^ 2 / 2 * M := by ring

end EllipticDirichlet.Poincare
