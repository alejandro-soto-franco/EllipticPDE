/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.Local.InteriorSmooth

/-!
# Infinite differentiability in the interior with classical hypotheses

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 3 (p. 334): "Assume
`a^{ij}, b^i, c ∈ C^∞(U)` and `f ∈ C^∞(U)`. Suppose `u ∈ H¹(U)` is a weak solution of the elliptic
PDE `Lu = f` in `U`. Then `u ∈ C^∞(U)`."

This file states the theorem on plain functions. The coefficients are smooth and uniformly
elliptic on the open set `U` with no bound (`SmoothOpOn`), the datum is smooth on `U`, and the
solution is a function `u` square-integrable on each compact subset of `U` with a weak gradient
`G`, square-integrable on each compact subset, satisfying the weak formulation against every
test function supported in `U` (`LocalWeakSol`). That is Evans's `u ∈ H¹_loc(U)`, which
`u ∈ H¹(U)` implies. Evans also asks `U` to be bounded and `a^{ij}` to be symmetric, and neither is
used here.

The proof is local. For each closed ball `B ⊆ U`, `localise` supplies an open `W ⊇ B` with
compact closure in `U`, a global operator agreeing with the given one on `W` and meeting every
regularity mixin, and a smooth compactly supported datum agreeing with `f` on `W`; the
restriction of `u` to `W` is then a local weak solution in `W12 W`
(`isLocalWeakSolution_of_localWeakSol`), `interior_smooth_global_W12` gives a representative
smooth on `W`, and `exists_contDiffOn_of_closedBall_ae` glues the balls.

## Main declarations

* `exists_contDiffOn_of_localWeakSol`: Evans's Theorem 3.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev EllipticPdes.Embedding

variable {n : ℕ}

/-- **Infinite differentiability in the interior (Evans, *Partial Differential Equations* (2nd
ed.), §6.3.1, Theorem 3, p. 334).** Let `U` be open, the coefficients `a^{ij}, b^i, c` smooth and
uniformly elliptic on `U` (`P : SmoothOpOn`), and `f` smooth on `U`. If `u` is square-integrable
on every compact subset of `U`, with a weak gradient `G` on `U` square-integrable on every compact
subset, and `u` solves `L u = f` weakly against every test function supported in `U`, then `u`
agrees almost everywhere on `U` with a function smooth on `U`. -/
theorem exists_contDiffOn_of_localWeakSol {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U) (P : SmoothOpOn (n + 1) U)
    {f u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {G : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hu : ∀ K, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K))
    (hG : ∀ i K, IsCompact K → K ⊆ U → MemLp (G i) 2 (volume.restrict K))
    (hgrad : HasWeakGradOn U u G)
    (hsol : LocalWeakSol U P.a P.b P.c f u G) :
    ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) u' U ∧ u' =ᵐ[volume.restrict U] u := by
  suffices h : ∃ u' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      u' =ᵐ[volume.restrict U] u ∧ ContDiffOn ℝ (⊤ : ℕ∞) u' U by
    obtain ⟨u', h1, h2⟩ := h
    exact ⟨u', h2, h1⟩
  refine exists_contDiffOn_of_closedBall_ae hU u fun x r _ hB => ?_
  obtain ⟨Op, W, f', hWo, hBW, hWc, hWU, -, ⟨hA1⟩, hk, hl, hf's, hf'c, -, hsolW⟩ :=
    localise P hU hf hsol (isCompact_closedBall x r) hB
  have hWm : MeasurableSet W := hWo.measurableSet
  have hWU' : W ⊆ U := subset_closure.trans hWU
  have hWcl : volume.restrict W ≤ volume.restrict (closure W) :=
    Measure.restrict_mono subset_closure le_rfl
  have huW : MemLp u 2 (volume.restrict W) := (hu _ hWc hWU).mono_measure hWcl
  have hGW : ∀ i, MemLp (G i) 2 (volume.restrict W) := fun i =>
    (hG i _ hWc hWU).mono_measure hWcl
  have hsolA := isLocalWeakSolution_of_localWeakSol Op huW hGW
    (memLp_iterPartial hf's hf'c W []) (hgrad.mono hWU') hsolW
  obtain ⟨v, hvae, hvc⟩ := interior_smooth_global_W12 Op hWm hWo hA1
    (fun k => Classical.choice (hk k)) (fun k => Classical.choice (hl k)) _ _
    (datum_hyp hf's hf'c W) hsolA
  have hball : Metric.ball x r ⊆ W := Metric.ball_subset_closedBall.trans hBW
  refine ⟨v, ?_, hvc.mono hball⟩
  have h0 : ((WithLp.toLp 2 (Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k)) : H1amb W) 0
      : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume.restrict W] u := by
    change ((Fin.cons (huW.toLp u) fun k => (hGW k).toLp (G k) : Fin (n + 2) → L2D W) 0
      : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[_] _
    rw [Fin.cons_zero]
    exact huW.coeFn_toLp
  have hext : (extendL2 hWm ((WithLp.toLp 2 (Fin.cons (huW.toLp u)
        fun k => (hGW k).toLp (G k)) : H1amb W) 0) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict W] u := by
    filter_upwards [ae_restrict_of_ae (coeFn_extendL2 hWm _), ae_restrict_mem hWm, h0]
      with y h1 h2 h3
    rw [h1, Set.indicator_of_mem h2, h3]
  exact (hvae.trans hext).filter_mono (ae_mono (Measure.restrict_mono hball le_rfl))

end EllipticPdes.Regularity
