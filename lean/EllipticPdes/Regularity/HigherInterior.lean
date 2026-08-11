/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.HigherWeakDeriv
import EllipticPdes.Regularity.LowerOrderWkInfty

/-!
# Higher interior regularity

Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(*Higher Interior Regularity*, p. 65). For a weak solution `u` of `L u = f` with
`a_{ij} ∈ W^{k+2,∞}`, `b_i, c ∈ W^{k+1,∞}` and `f ∈ H^k`, the solution lies in `H^{k+2}_loc`
with

`‖u‖_{H^{k+2}(V)} ≤ C (‖f‖_{H^k(Ω)} + ‖u‖_{L²(Ω)})` for every `V ⋐ Ω`,

the constant depending on the data and the pair `V ⋐ Ω` and on neither `u` nor `f`. Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 (p. 327) is the same statement
with `C^{k+1}` coefficients, which `IsCkCoeff.toIsWkInftyCoeff` shows to be the stronger
hypothesis.

## How the induction runs

`InteriorRegularityAt Op Ω k` packages the conclusion at order `k`, and the theorem is an
induction on `k` over that predicate.

* Order `0` is `interior_H2_estimate` with its `(k, i)`-indexed second derivatives assembled
  into a `HasIteratedWeakDerivOn` family of order `2`.
* The step differentiates the equation once. Where `u` solves `L u = f`, the derivative
  `∂_l u` solves `L (∂_l u) = ∂_l f + R_l`, with `R_l` collecting the terms in which the
  differentiation lands on a coefficient rather than on `u`. Those terms carry one derivative
  of a coefficient against derivatives of `u` of order at most two, so `R_l` sits in `H^{k-1}`
  once the order-`k-1` conclusion is available for `u` itself. Applying the induction
  hypothesis to `∂_l u` on an intermediate `V ⋐ W ⋐ Ω` gives `∂_l u ∈ H^{k+1}(V)`, which is
  `u ∈ H^{k+2}(V)`.

The differentiated equation is already available as
`EllipticPdes.Regularity.differentiated_weakForm_div`, and the admissibility of the test
function it needs as `interior_cutoffGrad_mem_H01`.

## Main declarations

* `InteriorRegularityAt`: the order-`k` conclusion, as a predicate, so that the induction has
  something to be an induction over.
* `interiorRegularityAt_zero`: the base case.
* `interiorRegularityAt_succ`: the induction step.
* `higher_interior_regularity`: the theorem.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **The order-`k` interior conclusion.** For every compact `V ⋐ Ω` there is a constant,
quantified before the solution and the datum, bounding every weak derivative of `u` of order at
most `k + 2` on `V` by `‖f‖_{H^k} + ‖u‖_{L²}`. The datum's `H^k` norm enters through a bound
`M` on its own iterated family, which `IteratedL2Bound.norm_le` shows to dominate `‖f‖`. -/
def InteriorRegularityAt (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (k : ℕ) : Prop :=
  ∀ {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}, IsCompact V → V ⊆ Ω →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : H01 Ω) (f : L2D Ω) (M : ℝ)
      (hfk : HasIteratedWeakDerivOn Ω k f), IteratedL2Bound hfk M →
      (∀ w : H01 Ω, Op.fullBilin Ω u w
        = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ)) →
      ∃ hu : HasIteratedWeakDerivOn V (k + 2)
          (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))),
        IteratedL2Bound hu (C * (M + ‖(u : H1amb Ω) 0‖))

/-- **Base case: order zero is the interior `H²` estimate.** The estimate
`interior_H2_estimate` returns, for each direction pair `(k, i)`, a weak `k`-derivative of
`∂ᵢu` on `V` together with its bound. Assembling those into a `HasIteratedWeakDerivOn` family
of order `2` is a matter of naming: the empty list is `u`, a singleton `[i]` is `∂ᵢu`, a pair
`[k, i]` is the returned `wki`, and longer lists are unconstrained because `D_step` is asked
only of lists shorter than `2`.

The first-order step, which the `H²` estimate does not itself provide, is
`hasWeakDeriv_extendL2_of_mem_H01`: the ambient encoding's coordinate `i.succ` is the weak
`i`-derivative of coordinate `0` on the whole space, and `hasWeakDerivOn_of_hasWeakDeriv`
localises it to `V`.

No constant is spent. The `H²` estimate bounds the sum of the three norms, so each of them is
bounded on its own, and `IteratedL2Bound.norm_le` supplies `‖f‖ ≤ M`. -/
theorem interiorRegularityAt_zero (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA : IsC1Coeff Op.toEllipticCoeff) :
    InteriorRegularityAt Op hΩm 0 := by
  classical
  intro V hVc hVΩ
  obtain ⟨C, hC0, hC⟩ := interior_H2_estimate Op hΩm hΩo hA hVc hVΩ
  refine ⟨C, hC0, fun u f M hfk hM hu => ?_⟩
  choose W hW hWb using hC u f hu
  -- The family: the empty list is `u`, a singleton is a first derivative, a pair is the
  -- second derivative the `H²` estimate returned. Longer lists are never asked about.
  refine ⟨⟨fun α =>
      match α with
      | [] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
      | [i] => restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) i.succ))
      | [k, i] => W k i
      | _ => 0, rfl, ?_⟩, ?_⟩
  · rintro m (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · exact hasWeakDerivOn_of_hasWeakDeriv m (hasWeakDeriv_extendL2_of_mem_H01 hΩm m u.2)
    · exact hW m i
    · simp at hα
  -- Each of the three norms is dominated by the sum the `H²` estimate bounds.
  · have hfM : ‖f‖ ≤ M := hM.norm_le
    have hshift : C * (‖f‖ + ‖(u : H1amb Ω) 0‖) ≤ C * (M + ‖(u : H1amb Ω) 0‖) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    rintro (_ | ⟨i, _ | ⟨j, rest⟩⟩) hα
    · refine le_trans ?_ hshift
      have h := hWb 0 0
      have h1 := norm_nonneg (W 0 0)
      have h2 := norm_nonneg (restrictL2 (Ω := V)
        (extendL2 hΩm ((u : H1amb Ω) (0 : Fin (n + 1)).succ)))
      linarith
    · refine le_trans ?_ hshift
      have h := hWb 0 i
      have h1 := norm_nonneg (W 0 i)
      have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
      linarith
    · rcases rest with _ | ⟨p, rest'⟩
      · refine le_trans ?_ hshift
        have h := hWb i j
        have h1 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) j.succ)))
        have h2 := norm_nonneg (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))
        linarith
      · simp at hα

/-- **Induction step.** Differentiating the equation once carries the order-`k` conclusion to
order `k + 1`, under one more order of regularity on every coefficient.

The step is Guo's, run one derivative at a time. Fix `V ⋐ Ω` and choose an intermediate
compact `W` with `V ⋐ W ⋐ Ω`. For each direction `l`, `differentiated_weakForm_div` presents
`∂_l u` as a weak solution on `W` of the same operator with datum `∂_l f + R_l`, where `R_l`
collects the terms in which `∂_l` lands on a coefficient. Every entry of `R_l` is a
coefficient derivative, essentially bounded by `IsWkInftyCoeff` and `IsWkInftyLower` at the
order in hand, multiplied by a derivative of `u` of order at most two, which the order-`0`
conclusion already controls on `W`. So `R_l` inherits an `H^k` bound from the order-`k`
conclusion applied to `u`, and the induction hypothesis applies to `∂_l u` with datum
`∂_l f + R_l`, giving `∂_l u ∈ H^{k + 2}(V)`. Reassembling over `l` through
`HasIteratedWeakDerivOn.deriv` read backwards gives `u ∈ H^{k + 3}(V)`. -/
theorem interiorRegularityAt_succ (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    {k : ℕ} (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3))
    (hbc : IsWkInftyLower Op (k + 2)) (hk : InteriorRegularityAt Op hΩm k) :
    InteriorRegularityAt Op hΩm (k + 1) := by
  sorry

/-- **Higher interior regularity (Guo, Theorem VIII.3.2, p. 65).** A weak solution with
`W^{k+2,∞}` principal coefficients, `W^{k+1,∞}` lower-order coefficients and an `H^k` datum has
weak derivatives of every order up to `k + 2` on each compact `V ⋐ Ω`, bounded by the data with
a constant quantified before the solution and the datum.

The coefficient hypotheses are asked at `k + 3` and `k + 2` rather than at `k + 2` and `k + 1`
because the induction consumes one order per step and the statement is proved for every order
at once; `IsWkInftyCoeff.mono` recovers the weaker form at any fixed `k`. -/
theorem higher_interior_regularity (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff) (k : ℕ)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3))
    (hbc : IsWkInftyLower Op (k + 2)) :
    InteriorRegularityAt Op hΩm k := by
  induction k with
  | zero => exact interiorRegularityAt_zero Op hΩm hΩo hA1
  | succ j ih =>
    refine interiorRegularityAt_succ (k := j) Op hΩm hΩo (hA.mono (by omega))
      (hbc.mono (by omega)) ?_
    exact ih (hA.mono (by omega)) (hbc.mono (by omega))

end EllipticPdes.Regularity
