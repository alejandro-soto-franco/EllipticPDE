/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.Garding
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Fredholm alternative for the elliptic Dirichlet problem

Evans §6.2.3, Theorem 4.

For the full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu` the Gårding inequality
makes the shifted form `B_γ = B + γ⟨·,·⟩_{L²}` coercive (`shiftedBilin_coercive`), so `L + γ` is
invertible by Lax-Milgram. Writing the solution operator of `L + γ` and the `L²` form as bounded
operators on `H₀¹(Ω)` reduces the weak problem `Lu = f` to a compact-operator equation
`(1 - K)u = h`, to which Mathlib's Fredholm alternative for compact operators
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) applies at the eigenvalue `1`.

The reduction is exact:

* `opA` / `opT`: the Riesz representatives of the full form `B` and of the `L²` form
  `⟨u₀, v₀⟩` as bounded operators on `H₀¹(Ω)` (`InnerProductSpace.continuousLinearMapOfBilin`),
  with `⟪opA u, v⟫ = B[u,v]` and `⟪opT u, v⟫ = ⟨u₀, v₀⟩`.
* `opE`: the coercive Lax-Milgram equivalence of `B_γ` (for `γ = gardingγ`), so
  `opA = opE - γ·opT` (`opA_eq`) and hence `opA = opE ∘ (1 - opK)` (`opA_factor`) with
  `opK = γ·opE⁻¹·opT`.
* `opA_eq_toDual_symm_iff`: the weak problem `B[u, ·] = f` is the equation `opA u = g` for the
  Riesz representative `g` of `f`.
-/

@[expose] public section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

namespace FullEllipticOp

variable (Op : FullEllipticOp d) (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-! ### Riesz representatives of the forms as bounded operators on `H₀¹(Ω)` -/

/-- The Riesz representative of the full divergence form `B` as an operator on `H₀¹(Ω)`:
`⟪opA u, v⟫ = B[u, v]`. -/
def opA : H01 Ω →L[ℝ] H01 Ω := continuousLinearMapOfBilin (Op.fullBilin Ω)

/-- The Riesz representative of the `L²` form `⟨u₀, v₀⟩` as an operator on `H₀¹(Ω)`. -/
def opT : H01 Ω →L[ℝ] H01 Ω := continuousLinearMapOfBilin (zerothForm Ω)

/-- The coercive Lax-Milgram equivalence of the shifted form `B_γ`, `γ = gardingγ`. -/
def opE : H01 Ω ≃L[ℝ] H01 Ω :=
  (Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)).continuousLinearEquivOfBilin

/-- Riesz identity: `⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v`. -/
lemma inner_opA (u v : H01 Ω) : ⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v :=
  continuousLinearMapOfBilin_apply (Op.fullBilin Ω) u v

/-- Riesz identity: `⟪opT Ω u, v⟫ = zerothForm Ω u v = ⟨u₀, v₀⟩_{L²}`. -/
lemma inner_opT (u v : H01 Ω) : ⟪opT Ω u, v⟫ = zerothForm Ω u v :=
  continuousLinearMapOfBilin_apply (zerothForm Ω) u v

/-- Riesz identity: `⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v`. -/
lemma inner_opE (u v : H01 Ω) :
    ⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v :=
  (Op.shiftedBilin_coercive Ω (le_refl Op.gardingγ)).continuousLinearEquivOfBilin_apply u v

/-! ### Reduction to `1 - opK` -/

/-- `opA = opE - γ·opT`: subtracting the shift recovers the unshifted form. -/
lemma opA_eq :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - Op.gardingγ • opT Ω := by
  refine ContinuousLinearMap.ext (fun u => ext_inner_right (𝕜 := ℝ) (fun v => ?_))
  rw [_root_.sub_apply, _root_.smul_apply, inner_sub_left,
    real_inner_smul_left, ContinuousLinearEquiv.coe_coe, Op.inner_opA Ω, Op.inner_opE Ω,
    inner_opT Ω, Op.shiftedBilin_apply, zerothForm_apply]
  ring

/-- The compact part of the reduction: `opK = γ·opE⁻¹·opT`. -/
def opK : H01 Ω →L[ℝ] H01 Ω :=
  Op.gardingγ • ((Op.opE Ω).symm : H01 Ω →L[ℝ] H01 Ω).comp (opT Ω)

/-- `opA = opE ∘ (1 - opK)`: the weak problem `Lu = f` becomes `(1 - opK)u = opE⁻¹(opA⁻¹…)`. -/
lemma opA_factor :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω) := by
  have hcomp : (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω)
      = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - Op.gardingγ • opT Ω := by
    refine ContinuousLinearMap.ext (fun u => ?_)
    simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
      one_apply_eq_self, _root_.smul_apply, opK,
      ContinuousLinearEquiv.coe_coe, map_sub, map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [Op.opA_eq Ω, hcomp]

/-- The weak problem `B[u, ·] = f` is the equation `opA u = g` for the Riesz representative `g`
of `f`. -/
lemma opA_eq_toDual_symm_iff (f : H01 Ω →L[ℝ] ℝ) (u : H01 Ω) :
    Op.opA Ω u = (InnerProductSpace.toDual ℝ (H01 Ω)).symm f
      ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = f v := by
  have hg : ∀ v, ⟪(InnerProductSpace.toDual ℝ (H01 Ω)).symm f, v⟫ = f v := fun v =>
    InnerProductSpace.toDual_symm_apply
  constructor
  · intro hu v
    rw [← Op.inner_opA Ω u v, hu, hg]
  · intro hu
    refine ext_inner_right (𝕜 := ℝ) (fun v => ?_)
    rw [Op.inner_opA Ω u v, hu v, hg]

end FullEllipticOp

end EllipticPdes.Sobolev
