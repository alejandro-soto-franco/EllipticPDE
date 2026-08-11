/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.HigherInterior
import EllipticPdes.Regularity.SmoothGlue

/-!
# Infinite differentiability in the interior

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (*Infinite
differentiability in the interior*, p. 331). Smooth coefficients and a smooth datum give a
solution smooth in the interior, whatever the boundary does.

The route is the one the chapter takes. Higher interior regularity, run at every order, puts
the solution in `H^m(V)` for every `m`; the Sobolev embedding then converts an unbounded supply
of weak derivatives into classical ones. Neither half needs a quantitative statement: the
constants of `higher_interior_regularity` are what make the estimate uniform, and smoothness on
a fixed `V` needs only that the derivatives exist.

## What the embedding half requires

`contDiffOn_interior_of_hasIteratedWeakDerivOn` is the missing analytic content, and it is two
steps rather than one.

* On a ball inside `V`, `H^{m}` with `m > 1 + (d/2)` puts the first weak derivatives in a
  Hölder class through `EllipticPdes.Embedding.morrey_ball`, after the Sobolev bootstrap
  `exists_eLpNorm_sobolevConj_le` has raised the exponent from `2` past `d`. The bootstrap has
  to be iterated: one Gagliardo-Nirenberg-Sobolev step raises `2` to `2d/(d-2)`, which passes
  `d` only for `d ≤ 3`, and the same ladder that opens dimensions four and up for the Hölder
  estimate opens them here.
* A function whose weak derivatives have continuous representatives is classically
  differentiable with those derivatives. Iterating that turns `H^m` for every `m` into
  `ContDiffOn ℝ ⊤`, and the representatives at successive orders agree because weak derivatives
  are unique almost everywhere, which is `EllipticPdes.Regularity.WeakDerivUnique`.

## Main declarations

* `contDiffOn_interior_of_hasIteratedWeakDerivOn`: weak derivatives of every order give a
  smooth representative on the interior.
* `interior_smooth`: Evans's Theorem 3.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **The Sobolev ladder on a ball.** An `L²` class carrying weak derivatives of every order
has a smooth representative on any ball whose closure sits inside the region.

This is the analytic content of Evans's Theorem 3, and it is two steps. The
Gagliardo-Nirenberg-Sobolev estimate `EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le`
raises the exponent from `2` to `2d/(d-2)`, which passes `d` only for `d ≤ 3`, so the ladder
has to be iterated before `EllipticPdes.Embedding.morrey_ball` puts a derivative of any fixed
order in a Hölder class. A function whose weak derivatives have continuous representatives is
then classically differentiable with those derivatives, and iterating that reads `H^m` for
every `m` as `C^∞`, the representatives at successive orders agreeing almost everywhere by
`EllipticPdes.Regularity.WeakDerivUnique`.

The closed ball rather than the open one is asked for because the Sobolev estimate is applied
to a cutoff of `u` supported in the region, and the cutoff needs room. -/
theorem exists_contDiffOn_ball_of_hasIteratedWeakDerivOn
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (u : L2D V)
    (h : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k u))
    {x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x r ⊆ interior V) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) v (Metric.ball x r) ∧
        v =ᵐ[volume.restrict (Metric.ball x r)]
          (u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) := by
  sorry

/-- **The Sobolev ladder, qualitative form.** An `L²` class on `V` carrying weak derivatives of
every order has a representative smooth on the interior of `V`. No bound is asked and none is
produced: the estimate lives in `higher_interior_regularity`, and smoothness on a fixed set
follows from the existence of the derivatives alone.

The proof is local, so it runs on balls inside `interior V` and never sees `V` itself except
through the family it is handed. `exists_contDiffOn_of_locally_ae` assembles the local
representatives, and it needs no gluing: two of them are continuous and agree almost everywhere
where their balls meet, so they agree there. -/
theorem contDiffOn_interior_of_hasIteratedWeakDerivOn
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (u : L2D V)
    (h : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k u)) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict (interior V)] (u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  refine exists_contDiffOn_of_locally_ae isOpen_interior _ fun y hy => ?_
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  refine ⟨Metric.ball y (r / 2), Metric.isOpen_ball, Metric.mem_ball_self (by linarith),
    (Metric.ball_subset_ball (by linarith)).trans hrsub, ?_⟩
  exact exists_contDiffOn_ball_of_hasIteratedWeakDerivOn u h (by linarith)
    ((Metric.closedBall_subset_ball (by linarith)).trans hrsub)

/-- **Infinite differentiability in the interior (Evans, §6.3.1, Theorem 3, p. 331).** For a
weak solution of `L u = f` whose coefficients lie in `W^{k,∞}` at every order and whose datum
has weak derivatives of every order in `L²(Ω)`, the solution has a representative smooth on the
interior of each compact `V ⋐ Ω`.

Smooth coefficients meet the hypothesis through `IsCkCoeff.toIsWkInftyCoeff` and
`IsWkInfty.ofContDiff`, so the classical statement with `a_{ij}, b_i, c, f ∈ C^∞(Ω)` is an
instance rather than a separate theorem. -/
theorem interior_smooth (Op : FullEllipticOp (n + 1))
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hΩm : MeasurableSet Ω) (hΩo : IsOpen Ω)
    (hA1 : IsC1Coeff Op.toEllipticCoeff)
    (hA : ∀ k : ℕ, IsWkInftyCoeff Op.toEllipticCoeff k)
    (hbc : ∀ k : ℕ, IsWkInftyLower Op k)
    (u : H01 Ω) (f : L2D Ω)
    (hf : ∀ k : ℕ, ∃ hfk : HasIteratedWeakDerivOn Ω k f, ∃ M : ℝ, IteratedL2Bound hfk M)
    (hweak : ∀ w : H01 Ω, Op.fullBilin Ω u w
      = ∫ x in Ω, (f x : ℝ) * ((w : H1amb Ω) 0 x : ℝ))
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hVc : IsCompact V) (hVΩ : V ⊆ Ω) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict (interior V)]
          (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) u' (interior V) := by
  -- Every order of weak differentiability on `V`, from higher interior regularity run at that
  -- order and then cut back down.
  have hall : ∀ k : ℕ, Nonempty (HasIteratedWeakDerivOn V k
      (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0)))) := by
    intro k
    obtain ⟨hfk, M, hM⟩ := hf k
    obtain ⟨C, _hC0, hC⟩ :=
      higher_interior_regularity Op hΩm hΩo hA1 k (hA (k + 3)) (hbc (k + 2)) hVc hVΩ
    obtain ⟨hu, _⟩ := hC u f M hfk hM hweak
    exact ⟨hu.mono (by omega)⟩
  obtain ⟨u', hu'ae, hu'smooth⟩ := contDiffOn_interior_of_hasIteratedWeakDerivOn _ hall
  refine ⟨u', ?_, hu'smooth⟩
  -- The `V`-restriction agrees almost everywhere with the whole-space extension it came from.
  have hres : (restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))
        : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (interior V)]
        (extendL2 hΩm ((u : H1amb Ω) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    (coeFn_restrictL2 (Ω := V) (extendL2 hΩm ((u : H1amb Ω) 0))).filter_mono
      (ae_mono (Measure.restrict_mono interior_subset le_rfl))
  exact hu'ae.trans hres

end EllipticPdes.Regularity
