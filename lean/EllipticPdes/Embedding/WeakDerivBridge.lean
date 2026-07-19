/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Embedding.WeakGradient
import EllipticPdes.Regularity.Interior

/-!
# Bridge: `HasWeakDerivOn` to `HasWeakGradOn`

The `L²` weak derivatives produced by `interior_H2_estimate` are honest-function weak
gradients in the sense of the embedding layer, so the Morrey inequality consumes them
directly (for `p = 2`, hence `d = 1`; general `d` needs a separate `Lᵖ` bootstrap).
-/

open MeasureTheory Set Metric

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- An `L²` weak gradient (componentwise `HasWeakDerivOn`) is an honest-function weak
gradient. This connects `interior_H2_estimate`'s output into `morrey_ball`. -/
theorem hasWeakGradOn_of_hasWeakDerivOn {B : Set (EuclideanSpace ℝ (Fin d))}
    {u : Lp ℝ 2 (volume.restrict B)} {g : Fin d → Lp ℝ 2 (volume.restrict B)}
    (h : ∀ k, EllipticPdes.Regularity.HasWeakDerivOn B k u (g k)) :
    HasWeakGradOn B (fun x => (u x : ℝ)) (fun k x => (g k x : ℝ)) := by
  intro φ hφc hφcs hφB k
  exact h k φ hφc hφcs hφB

end EllipticPdes.Embedding
