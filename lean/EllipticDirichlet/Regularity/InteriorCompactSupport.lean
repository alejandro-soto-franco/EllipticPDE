/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Regularity.Caccioppoli
import Mathlib.Analysis.FunctionalSpaces.LpExtendByZero

/-!
# The whole-space extension bridge for the interior `H²` estimate

The interior second-derivative estimate (Evans, *Partial Differential Equations* (2nd ed.),
§6.3.1; Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8) runs the
difference-quotient method of the whole-space engine
(`EllipticDirichlet.Regularity.DifferenceQuotient`,
`EllipticDirichlet.Regularity.DiffQuotientBound`) against the restricted-domain weak
solution and its Caccioppoli energy bound
(`EllipticDirichlet.Regularity.Caccioppoli`).

The two layers live on different measures: the difference-quotient engine is built on the
whole-space space `EucL2 d = Lp ℝ 2 volume`, while the weak solution, the cutoff
multiplication keystone, and the Caccioppoli estimate live on the restricted-domain space
`L2D Ω = Lp ℝ 2 (volume.restrict Ω)`. This file provides the load-bearing bridge between
them: extension by zero `L2D Ω →ₗᵢ[ℝ] EucL2 d`, packaged from the Mathlib linear isometry
`MeasureTheory.lpExtendByZero`, together with the compatibility that carries the
cutoff-weighted gradient energy of the Caccioppoli estimate onto whole-space `EucL2 d`
classes with the `L²` norm preserved.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Regularity

open EllipticDirichlet.Sobolev

variable {d : ℕ}

/-! ### Extension by zero as the restricted-to-whole-space bridge -/

/-- **Extension by zero**, `L2D Ω →ₗᵢ[ℝ] EucL2 d`. A class on the restricted measure
`volume.restrict Ω` is carried to the whole-space `L²(ℝ^d)` class of its extension by zero,
with the `L²` norm preserved. This is the substrate bridge that lets the whole-space
difference-quotient engine act on restricted-domain gradient data (Evans, *Partial
Differential Equations* (2nd ed.), §6.3.1). -/
def extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω) :
    L2D Ω →ₗᵢ[ℝ] EucL2 d :=
  lpExtendByZero volume 2 Ω hΩm

/-- The a.e. representative of the extension by zero: `extendL2 hΩm g =ᵐ Ω.indicator g`. -/
theorem coeFn_extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) :
    (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume] Ω.indicator (g : EuclideanSpace ℝ (Fin d) → ℝ) :=
  coeFn_lpExtendByZero hΩm g

/-- The extension by zero preserves the `L²` norm: `‖extendL2 hΩm g‖ = ‖g‖`. -/
theorem norm_extendL2 {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) : ‖extendL2 hΩm g‖ = ‖g‖ :=
  (extendL2 hΩm).norm_map g

/-- The extension by zero vanishes almost everywhere off `Ω`. -/
theorem extendL2_ae_eq_zero {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    (g : L2D Ω) :
    ∀ᵐ x ∂volume, x ∉ Ω → (extendL2 hΩm g : EuclideanSpace ℝ (Fin d) → ℝ) x = 0 :=
  lpExtendByZero_ae_eq_zero hΩm g

/-! ### Carrying the Caccioppoli energy onto whole-space classes -/

/-- **The Caccioppoli energy, on whole-space classes.** Feeding the interior energy estimate
`EllipticDirichlet.Regularity.caccioppoli` through the norm-preserving extension bridge, the
cutoff-weighted gradient energy of a weak solution `u ∈ H₀¹(Ω)` of `L u = f`, measured on the
whole-space `EucL2 d` classes `extendL2 hΩm (ζ · ∂ᵢu)`, is bounded by the data:
`(λ/2) ∑ᵢ ‖extendL2 hΩm (ζ · ∂ᵢu)‖² ≤ C (‖f‖² + ‖u₀‖²)`. These whole-space classes are the
gradient data on which the difference-quotient method of the interior second-derivative
estimate operates (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg-Trudinger, *Elliptic PDE of Second Order*, Theorem 8.8). -/
theorem extendL2_cutoffGrad_energy_le (Op : FullEllipticOp d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {ζ : EuclideanSpace ℝ (Fin d) → ℝ} (hζ : IsTestFn Ω ζ) (u : H01 Ω) (f : L2D Ω)
    (hu : ∀ v : H01 Ω, Op.fullBilin Ω u v
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      Op.lam / 2 * ∑ i : Fin d, ‖extendL2 hΩm (mulTest hζ ((u : H1amb Ω) i.succ))‖ ^ 2
        ≤ C * (‖f‖ ^ 2 + ‖(u : H1amb Ω) 0‖ ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := caccioppoli Op hζ u f hu
  refine ⟨C, hC0, ?_⟩
  have hnorm : ∀ i : Fin d,
      ‖extendL2 hΩm (mulTest hζ ((u : H1amb Ω) i.succ))‖
        = ‖mulTest hζ ((u : H1amb Ω) i.succ)‖ :=
    fun i => norm_extendL2 hΩm _
  simp_rw [hnorm]
  exact hC

end EllipticDirichlet.Regularity
