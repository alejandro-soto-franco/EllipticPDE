/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.OperatorBackground
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak compactness in reflexive spaces

Brezis (`brezis-2011-fun-ana-sob`, Theorem 3.17 (Kakutani), p. 67) shows that the closed unit
ball of a reflexive Banach space is compact in the weak topology. Mazur's theorem (Theorem 3.7,
p. 60) says that a convex set is weakly closed exactly when it is norm closed. Together they give
weak compactness of every bounded closed convex set, which is the compactness input of the direct
method of the calculus of variations.

Mathlib has Banach–Alaoglu (`WeakDual.isCompact_closedBall`), Mazur
(`Convex.toWeakSpace_closure`) and the transfer `NormedSpace.isCompact_closure_of_isBounded`
from the weak-star bidual back to the weak topology. It has no statement for reflexive spaces,
so the three results below supply it.

## Main declarations

* `EllipticPdes.isCompact_toWeakSpace_closedBall`: a closed ball of a reflexive Banach space is
  weakly compact.
* `EllipticPdes.isClosed_toWeakSpace_of_convex`: a norm-closed convex set is weakly closed.
* `EllipticPdes.isCompact_toWeakSpace_of_bounded_convex_closed`: a bounded closed convex set in a
  reflexive Banach space is weakly compact.
-/

@[expose] public section

open Metric

namespace EllipticPdes

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Mazur.** A norm-closed convex set is closed in the weak topology (Brezis, Theorem 3.7,
p. 60). -/
theorem isClosed_toWeakSpace_of_convex {K : Set X} (hK : Convex ℝ K) (hc : IsClosed K) :
    IsClosed (toWeakSpace ℝ X '' K) := by
  rw [← closure_eq_iff_isClosed, ← Convex.toWeakSpace_closure ℝ hK, hc.closure_eq]

/-- **Kakutani.** A closed ball of a reflexive Banach space is compact in the weak topology
(Brezis, Theorem 3.17, p. 67). -/
theorem isCompact_toWeakSpace_closedBall (hX : Analysis.IsReflexive X)
    (r : ℝ) : IsCompact (toWeakSpace ℝ X '' closedBall 0 r) := by
  have hconv : Convex ℝ (closedBall (0 : X) r) := convex_closedBall 0 r
  have hcl := isClosed_toWeakSpace_of_convex hconv isClosed_closedBall
  have key := NormedSpace.isCompact_closure_of_isBounded ℝ X
    (toWeakSpace ℝ X '' closedBall 0 r)
    (by
      simpa [Set.preimage_image_eq _ (toWeakSpace ℝ X).injective] using
        isBounded_closedBall (x := (0 : X)) (r := r))
    (by
      have hsub : NormedSpace.inclusionInDoubleDualWeak ℝ X '' (toWeakSpace ℝ X '' closedBall 0 r)
          ⊆ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ (StrongDual ℝ X)) r := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        rw [Set.mem_preimage]
        have h : WeakDual.toStrongDual
            (NormedSpace.inclusionInDoubleDualWeak ℝ X (toWeakSpace ℝ X x)) =
            NormedSpace.inclusionInDoubleDual ℝ X x := by
          ext f
          simp [NormedSpace.inclusionInDoubleDualWeak_apply]
        rw [h]
        have h2 : NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X) x ∈
            closedBall (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X) 0) r := by
          rw [← Set.mem_preimage, LinearIsometry.preimage_closedBall]
          exact hx
        rw [show NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X) 0 = 0 from
          (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := X)).toLinearMap.map_zero] at h2
        exact h2
      refine (closure_minimal hsub (WeakDual.isClosed_closedBall _ _)).trans ?_
      intro φ _
      obtain ⟨x, hx⟩ := hX (WeakDual.toStrongDual φ)
      refine ⟨toWeakSpace ℝ X x, ?_⟩
      apply WeakDual.toStrongDual.injective
      ext f
      exact congrArg (fun ψ => ψ f) hx)
  rwa [hcl.closure_eq] at key

/-- A bounded, norm-closed convex subset of a reflexive Banach space is compact in the weak
topology (Brezis, Theorems 3.7 and 3.17, pp. 60 and 67). -/
theorem isCompact_toWeakSpace_of_bounded_convex_closed
    (hX : Analysis.IsReflexive X) {K : Set X} (hK : Convex ℝ K) (hc : IsClosed K)
    (hb : Bornology.IsBounded K) : IsCompact (toWeakSpace ℝ X '' K) := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : X)).mp hb
  exact (isCompact_toWeakSpace_closedBall hX r).of_isClosed_subset
    (isClosed_toWeakSpace_of_convex hK hc) (Set.image_mono hr)

end EllipticPdes
