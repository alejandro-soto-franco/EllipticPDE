/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Regularity.DifferentiatedEquation
import EllipticPdes.Regularity.LeibnizWkInfty
import EllipticPdes.Regularity.LowerOrderWkInfty

/-!
# Moving a derivative onto the solution, under Guo's coefficient hypothesis

`EllipticPdes.Regularity.principal_move`, `transport_move` and `zeroth_move` carry `∂_ℓ` from the
test function onto the solution in the three terms of the equation, each by one application of
the Leibniz rule for a `C¹` weight. Guo, *Partial Differential Equations I and II* (Course
Lecture Notes), Theorem VIII.3.2 (p. 65) asks only for `W^{k,∞}` coefficients, which carry no
classical derivative, and this file repeats the three with `HasWeakDerivOn.mul_isWkInfty_left`
in place of `HasWeakDerivOn.mul_contDiff_left`.

The statements differ from their `C¹` counterparts in one place: where those write
`partialD ℓ (fun y => A.a y i j)` for the derivative of a coefficient, these write the chosen
representative `hA.D [ℓ] i j` that `IsWkInftyCoeff` carries. Everything else is unchanged, so a
consumer that reaches for the commutator by name sees the same shape.

## Main declarations

* `principal_move_wkInfty`: the principal term, for `a ∈ W^{1,∞}`.
* `transport_move_wkInfty`: the transport term, for `b_i ∈ W^{1,∞}`.
* `zeroth_move_wkInfty`: the zeroth-order term, for `c ∈ W^{1,∞}`.
-/

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-! ### Reading the order-one data off a `W^{k,∞}` bundle -/

namespace IsWkInftyCoeff

variable {A : EllipticCoeff d} {k : ℕ}

/-- The coefficient entry is measurable, read off the order-zero member of the family. -/
theorem measurable_coeff (hA : IsWkInftyCoeff A k) (i j : Fin d) :
    Measurable (fun x => A.a x i j) := by
  have h := hA.D_meas i j [] (by simp)
  rwa [hA.D_nil i j] at h

/-- The order-one member of the family is a weak partial derivative of the coefficient entry. -/
theorem hasWeakPartial_D (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    HasWeakPartial ℓ (fun x => A.a x i j) (hA.D [ℓ] i j) := by
  have h := hA.D_step i j ℓ [] (by simp)
  rwa [hA.D_nil i j] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    Measurable (hA.D [ℓ] i j) := hA.D_meas i j [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hA : IsWkInftyCoeff A (k + 1)) (ℓ i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hA.D [ℓ] i j x| ≤ hA.bound 1 := by
  have h := hA.ess_bdd i j [ℓ] (by simp)
  simpa using h

end IsWkInftyCoeff

namespace IsWkInfty

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ}

/-- The function is measurable, read off the order-zero member of the family. -/
theorem measurable_self (hf : IsWkInfty f k) : Measurable f := by
  have h := hf.D_meas [] (by simp)
  rwa [hf.D_nil] at h

/-- The function is essentially bounded by `bound 0`. -/
theorem ae_abs_le (hf : IsWkInfty f k) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |f x| ≤ hf.bound 0 := by
  have h := hf.ess_bdd [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is a weak partial derivative of the function. -/
theorem hasWeakPartial_D (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    HasWeakPartial ℓ f (hf.D [ℓ]) := by
  have h := hf.D_step ℓ [] (by simp)
  rwa [hf.D_nil] at h

/-- The order-one member of the family is measurable. -/
theorem measurable_D_singleton (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    Measurable (hf.D [ℓ]) := hf.D_meas [ℓ] (by simp)

/-- The order-one member of the family is essentially bounded by `bound 1`. -/
theorem ae_abs_D_singleton_le (hf : IsWkInfty f (k + 1)) (ℓ : Fin d) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |hf.D [ℓ] x| ≤ hf.bound 1 := by
  have h := hf.ess_bdd [ℓ] (by simp)
  simpa using h

end IsWkInfty

/-! ### The three terms -/

/-- **Principal term, for a `W^{1,∞}` coefficient.** For every direction pair the weighted first
derivative `a_{ij}·∂ᵢu` has weak `ℓ`-derivative `(∂_ℓ a_{ij})·∂ᵢu + a_{ij}·∂_ℓ∂ᵢu`, with the
coefficient derivative read off the family rather than taken classically. Testing against `∂ⱼφ`
and summing gives
`∑ ∫_V a_{ij}(∂ᵢu) ∂_ℓ∂ⱼφ = -∑ ∫_V [(∂_ℓ a_{ij})(∂ᵢu) + a_{ij}(∂ₗ∂ᵢu)] ∂ⱼφ`. -/
theorem principal_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))}
    {A : EllipticCoeff d} {k : ℕ} (hA : IsWkInftyCoeff A (k + 1)) (ℓ : Fin d)
    (Du : Fin d → Lp ℝ 2 (volume.restrict V))
    (D2 : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hD2 : ∀ i, HasWeakDerivOn V ℓ (Du i) (D2 ℓ i))
    (aDu : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (haDu : ∀ i j, aDu i j =ᵐ[volume.restrict V] fun x => A.a x i j * (Du i x : ℝ))
    (comm : Fin d → Fin d → Lp ℝ 2 (volume.restrict V))
    (hcomm : ∀ i j, comm i j =ᵐ[volume.restrict V] fun x =>
      hA.D [ℓ] i j x * (Du i x : ℝ) + A.a x i j * (D2 ℓ i x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
  have hstep : ∀ i j : Fin d,
      ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
        = - ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
    intro i j
    have hmove := HasWeakDerivOn.mul_isWkInfty_left ℓ (hD2 i)
      (hA.measurable_coeff i j) (hA.measurable_D_singleton ℓ i j) (hA.hasWeakPartial_D ℓ i j)
      (A.bdd i j) (hA.ae_abs_D_singleton_le ℓ i j) (aDu i j) (haDu i j) (comm i j) (hcomm i j)
    obtain ⟨hψc, hψcs, hψV⟩ := isTest_partialD hφc hφcs hφV j
    exact hmove (partialD j φ) hψc hψcs hψV
  calc ∑ i, ∑ j, ∫ x in V, (aDu i j x : ℝ) * partialD ℓ (partialD j φ) x
      = ∑ i : Fin d, ∑ j : Fin d, - ∫ x in V, (comm i j x : ℝ) * partialD j φ x :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))
    _ = - ∑ i, ∑ j, ∫ x in V, (comm i j x : ℝ) * partialD j φ x := by
        simp only [Finset.sum_neg_distrib]

/-- **Transport term, for a `W^{1,∞}` coefficient.**
`∫_V b_i(∂ᵢu) ∂_ℓφ = -∫_V [(∂_ℓ b_i)(∂ᵢu) + b_i(∂ₗ∂ᵢu)] φ`, with the coefficient derivative read
off the family. -/
theorem transport_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {bi : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ} (hbi : IsWkInfty bi (k + 1))
    (Du_i D2_ℓi : Lp ℝ 2 (volume.restrict V)) (hD2 : HasWeakDerivOn V ℓ Du_i D2_ℓi)
    (bDu : Lp ℝ 2 (volume.restrict V))
    (hbDu : bDu =ᵐ[volume.restrict V] fun x => bi x * (Du_i x : ℝ))
    (comm : Lp ℝ 2 (volume.restrict V))
    (hcomm : comm =ᵐ[volume.restrict V]
      fun x => hbi.D [ℓ] x * (Du_i x : ℝ) + bi x * (D2_ℓi x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (bDu x : ℝ) * partialD ℓ φ x = - ∫ x in V, (comm x : ℝ) * φ x :=
  HasWeakDerivOn.mul_isWkInfty_left ℓ hD2 hbi.measurable_self (hbi.measurable_D_singleton ℓ)
    (hbi.hasWeakPartial_D ℓ) hbi.ae_abs_le (hbi.ae_abs_D_singleton_le ℓ) bDu hbDu comm hcomm
    φ hφc hφcs hφV

/-- **Zeroth-order term, for a `W^{1,∞}` coefficient.**
`∫_V c·u·∂_ℓφ = -∫_V [(∂_ℓ c)·u + c·(∂ₗu)] φ`, with the coefficient derivative read off the
family. -/
theorem zeroth_move_wkInfty {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} {k : ℕ} (hc : IsWkInfty c (k + 1))
    (u_V Du_ℓ : Lp ℝ 2 (volume.restrict V)) (hDu : HasWeakDerivOn V ℓ u_V Du_ℓ)
    (cu : Lp ℝ 2 (volume.restrict V))
    (hcu : cu =ᵐ[volume.restrict V] fun x => c x * (u_V x : ℝ))
    (comm : Lp ℝ 2 (volume.restrict V))
    (hcomm : comm =ᵐ[volume.restrict V]
      fun x => hc.D [ℓ] x * (u_V x : ℝ) + c x * (Du_ℓ x : ℝ))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (cu x : ℝ) * partialD ℓ φ x = - ∫ x in V, (comm x : ℝ) * φ x :=
  HasWeakDerivOn.mul_isWkInfty_left ℓ hDu hc.measurable_self (hc.measurable_D_singleton ℓ)
    (hc.hasWeakPartial_D ℓ) hc.ae_abs_le (hc.ae_abs_D_singleton_le ℓ) cu hcu comm hcomm
    φ hφc hφcs hφV

end EllipticPdes.Regularity
