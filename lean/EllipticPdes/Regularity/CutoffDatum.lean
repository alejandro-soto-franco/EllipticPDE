/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.DatumPiece
import EllipticPdes.Regularity.LocalWeakFormWkInfty

/-!
# The datum of the induction step

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 step 3 produces an equation
for the cut-off derivative whose datum is a fixed list of shapes. Each is the middle cutoff of
the tower, or one of its first two partial derivatives, against a coefficient of the operator or
one of its derivatives, against a derivative of the solution of order at most two.

This file builds that datum as a single `L²(Ω)` class, with its order-`k` family, its bound and
its pairing. Nothing here knows how the list arose: the expansion of the bilinear form and the
differentiated equation both live in `EllipticPdes.Regularity.HigherInterior`, and what they
need of the datum is exactly the three conclusions below.

The constant is quantified before the solution, the datum and the direction of differentiation.
The shapes that differentiate a coefficient in the direction the equation is differentiated
depend on that direction, so their constants are collected over it.

## Main declarations

* `exists_cutoffDatum`: the datum, its family, its bound and its pairing.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
-- Thirteen shapes over one and two directions, each carrying a bundle of weak derivatives.
/-- **The datum of the induction step.** For a cutoff `ξ` supported in the collar `N ⊆ Ω`, there
is a constant such that every family of derivatives of the solution on `N` bounded by `B`, and
every derivative of the datum bounded by `B`, produce an `L²(Ω)` class carrying `k` weak
derivatives bounded by `K·B` and pairing against a test function as the thirteen shapes.

The two shapes carrying the zeroth-order coefficient against the differentiated solution cancel
between the differentiated equation and the zeroth-order block, and are absent. The two carrying
the transport coefficient do not, because the equation names one order of differentiation and
the block the other, and only the symmetry of the mixed second derivatives identifies them. -/
theorem exists_cutoffDatum (Op : FullEllipticOp (n + 1))
    {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω) {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 3)) (hbc : IsWkInftyLower Op (k + 2))
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : Fin (n + 1)) (uN Df : L2D N)
      (HuN : HasIteratedWeakDerivOn N (k + 2) uN)
      (HDf : HasIteratedWeakDerivOn N k Df) (B : ℝ),
      IteratedL2Bound HuN B → IteratedL2Bound HDf B →
      ∃ (F : L2D Ω) (HF : HasIteratedWeakDerivOn Ω k F),
        IteratedL2Bound HF (K * B) ∧
        ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v →
          HasCompactSupport v →
          (∫ x in Ω, (F x : ℝ) * v x)
            = (∫ x in N, ξ x * ((1 : ℝ) * (Df x : ℝ)) * v x)
              - (∑ i, ∫ x in N, ξ x * ((hbc.bReg i).D [ℓ] x * (HuN.D [i] x : ℝ)) * v x)
              - (∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [ℓ, i] x : ℝ)) * v x)
              - (∫ x in N, ξ x * (hbc.cReg.D [ℓ] x * (HuN.D [] x : ℝ)) * v x)
              + (∑ i, ∑ j, ∫ x in N,
                  ξ x * (((hA.entry i j).deriv ℓ).D [j] x * (HuN.D [i] x : ℝ)) * v x)
              + (∑ i, ∑ j, ∫ x in N,
                  ξ x * ((hA.entry i j).D [ℓ] x * (HuN.D [j, i] x : ℝ)) * v x)
              - (∑ i, ∑ j, ∫ x in N,
                  partialD j ξ x * (Op.a x i j * (HuN.D [i, ℓ] x : ℝ)) * v x)
              - (∑ i, ∑ j, ∫ x in N,
                  partialD j (partialD i ξ) x * (Op.a x i j * (HuN.D [ℓ] x : ℝ)) * v x)
              - (∑ i, ∑ j, ∫ x in N,
                  partialD i ξ x * ((hA.entry i j).D [j] x * (HuN.D [ℓ] x : ℝ)) * v x)
              - (∑ i, ∑ j, ∫ x in N,
                  partialD i ξ x * (Op.a x i j * (HuN.D [j, ℓ] x : ℝ)) * v x)
              + (∑ i, ∫ x in N, partialD i ξ x * (Op.b x i * (HuN.D [ℓ] x : ℝ)) * v x)
              + ∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [i, ℓ] x : ℝ)) * v x := by
  classical
  sorry

end EllipticPdes.Regularity
