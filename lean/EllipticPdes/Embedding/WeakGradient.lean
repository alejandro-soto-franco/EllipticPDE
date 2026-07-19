/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Sobolev.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Average

/-!
# Honest-function weak gradients on a set

The `Lᵖ`-scale, honest-function analogue of `HasWeakDerivOn`: a function `u` has weak
gradient `g = (gₖ)` on `B` when integration by parts holds against every smooth test
function supported in `B`. This is the interface the Morrey embedding consumes; it is
stated for honest functions (not `Lp` classes) and for a full gradient tuple so that a
general exponent `p > d` is expressible, which the `L²`-only `HasWeakDerivOn` cannot do.
-/

open MeasureTheory Set Metric
open scoped NNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD)

variable {d : ℕ}

/-- `g` is the honest-function weak gradient of `u` on `B`: integration by parts holds
against every smooth compactly supported test function whose support lies in `B`. This
mirrors `EllipticPdes.Regularity.HasWeakDerivOn` component-wise but for honest
functions `u, gₖ : EuclideanSpace ℝ (Fin d) → ℝ`. -/
def HasWeakGradOn (B : Set (EuclideanSpace ℝ (Fin d)))
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ B → ∀ k : Fin d,
      ∫ x in B, u x * partialD k φ x = - ∫ x in B, g k x * φ x

/-- The Morrey/Hölder exponent `γ = 1 - d/p`, as a `ℝ≥0` (faithful when `p > d`). -/
def morreyExponent (d : ℕ) (p : ℝ) : ℝ≥0 := Real.toNNReal (1 - (d : ℝ) / p)

/-- When `p > d`, the Morrey exponent coerces back to `1 - d/p`. -/
theorem coe_morreyExponent {p : ℝ} (hp : (d : ℝ) < p) (hd : 0 < d) :
    (morreyExponent d p : ℝ) = 1 - (d : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hp
  have : 0 ≤ 1 - (d : ℝ) / p := by
    rw [sub_nonneg, div_le_one hp0]; exact hp.le
  simp [morreyExponent, Real.coe_toNNReal _ this]

end EllipticPdes.Embedding
