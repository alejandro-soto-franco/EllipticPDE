/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Poincare.BoxSlice
public import EllipticPdes.Poincare.GraphBounded
public import EllipticPdes.Sobolev.GraphEuclidean

/-!
# Poincaré inequality on arbitrary bounded domains (chain step 5)

The Poincaré inequality on `H₀¹(Ω)` for bounded `Ω` is the transport, along `h01Equiv`, of the
inequality on the graph space `H1Graph.H01 volume Ω` (`H1Graph.poincare_H01_of_bounded`). This is
the `p = q = 2` Friedrichs inequality, and it gives the coercivity of the Dirichlet form of the
Laplacian on a bounded domain (`laplaceBilin_coercive_of_bounded`).
-/

@[expose] public section

open MeasureTheory Set

noncomputable section

namespace EllipticPdes.Poincare

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Poincaré inequality on `H₀¹` of an arbitrary bounded domain** (the
Friedrichs inequality, `p = q = 2`): some constant `C ≥ 0` controls the function part
by the gradient part, uniformly over `H₀¹(Ω)`.

Guo, *Partial Differential Equations* (JHU AS.110.631-632), Theorem III.4.6 states the
`W_0^{1,p}` form, `‖u‖_{L^q} ≤ C ‖Du‖_{L^p}` for `q ∈ [1, p*]`, and derives it from the
Gagliardo-Nirenberg-Sobolev inequality. This declaration is its `p = q = 2` case, proved
on a different route and consequently in every dimension: Guo's hypothesis `p ∈ [1, n)`
reads `n > 2` at `p = 2`, excluding `n = 1` and `n = 2`, because the GNS route needs a
finite Sobolev conjugate. The route here goes through the slab Poincaré inequality
`integral_sq_le_of_tsupport_subset_slab`, which asks nothing of the dimension, with a constant
depending only on the radius of a ball containing `Ω`, in place of the sharp one. -/
theorem poincare_H01_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H1amb Ω), U ∈ H01 Ω →
      ‖U 0‖ ^ 2 ≤ C * ∑ i : Fin (n + 1), ‖U i.succ‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := H1Graph.poincare_H01_of_bounded (μ := (volume : Measure _)) hΩb
  refine ⟨C, hC, fun U hU => ?_⟩
  have := h _ (H1Graph.h01Equiv Ω ⟨U, hU⟩).2
  rwa [H1Graph.fnL_h01Equiv, H1Graph.norm_gradL_h01Equiv_sq] at this

/-- **Coercivity of the bilinear form of the Laplacian on a bounded domain**, with no abstract
Poincaré
hypothesis. `poincare_H01_of_bounded` names the constant, so the only input is boundedness of
`Ω`. This is the form of coercivity the direct method uses, where the domain is a ball and no
box structure is at hand. -/
theorem laplaceBilin_coercive_of_bounded {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω) : IsCoercive (EllipticPdes.laplaceBilin Ω) := by
  obtain ⟨C, hC, hpoin⟩ := poincare_H01_of_bounded hΩb
  refine ⟨1 / (C + 1), by positivity, fun U => ?_⟩
  exact isCoercive_of_energy_le (H01 Ω) one_pos hC
    (fun V => by rw [EllipticPdes.laplaceBilin_self, one_mul]; rfl)
    (fun V => hpoin (V : H1amb Ω) V.2) U

end EllipticPdes.Poincare
