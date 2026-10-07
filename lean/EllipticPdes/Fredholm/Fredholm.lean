/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.Garding
public import EllipticPdes.Fredholm.GardingForm
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# Fredholm alternative for the elliptic Dirichlet problem

Evans §6.2.3, Theorem 4.

For the full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu` the Gårding inequality
makes the shifted form `B_γ = B + γ⟨·,·⟩_{L²}` coercive (`shiftedBilin_coercive`). The operator
is therefore an abstract `GardingForm` on `H₀¹(Ω)` over `L²(Ω)` (`gardingForm`), and the
reduction of the weak problem `Lu = f` to the compact-operator equation `(1 - K)u = h` is the
one proved in `GardingForm.lean`; this file names its pieces for the elliptic operator.

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

/-! ### The Gårding form of the operator -/

/-- The operator `Op` on `H₀¹(Ω)` as an abstract Gårding form over `L²(Ω)`: the form is
`fullBilin`, the embedding is `U ↦ U₀`, and the constants are `λ/2` and `gardingγ`. -/
def gardingForm : GardingForm (H01 Ω) (L2D Ω) where
  form := Op.fullBilin Ω
  emb := coordL Ω 0
  β := Op.lam / 2
  γ := Op.gardingγ
  β_pos := half_pos Op.lam_pos
  γ_pos := Op.gardingγ_pos
  garding := Op.garding Ω

/-! ### Riesz representatives of the forms as bounded operators on `H₀¹(Ω)` -/

/-- The Riesz representative of the full divergence form `B` as an operator on `H₀¹(Ω)`:
`⟪opA u, v⟫ = B[u, v]`. -/
def opA : H01 Ω →L[ℝ] H01 Ω := (Op.gardingForm Ω).opA

/-- The Riesz representative of the `L²` form `⟨u₀, v₀⟩` as an operator on `H₀¹(Ω)`. -/
def opT : H01 Ω →L[ℝ] H01 Ω := continuousLinearMapOfBilin (zerothForm Ω)

/-- The coercive Lax-Milgram equivalence of the shifted form `B_γ`, `γ = gardingγ`. -/
def opE : H01 Ω ≃L[ℝ] H01 Ω := (Op.gardingForm Ω).opE

/-- The compact part of the reduction: `opK = γ·opE⁻¹·opT`. -/
def opK : H01 Ω →L[ℝ] H01 Ω :=
  Op.gardingγ • ((Op.opE Ω).symm : H01 Ω →L[ℝ] H01 Ω).comp (opT Ω)

/-- The abstract `opT` of the Gårding form is the Riesz operator of the `L²` form. -/
lemma gardingForm_opT : (Op.gardingForm Ω).opT = opT Ω := rfl

/-- The abstract `opK` of the Gårding form is `opK`. -/
lemma gardingForm_opK : (Op.gardingForm Ω).opK = Op.opK Ω := rfl

/-- The shifted form of the Gårding form is `shiftedBilin` at `gardingγ`. -/
lemma gardingForm_shifted : (Op.gardingForm Ω).shifted = Op.shiftedBilin Ω Op.gardingγ := rfl

/-- Riesz identity: `⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v`. -/
lemma inner_opA (u v : H01 Ω) : ⟪Op.opA Ω u, v⟫ = Op.fullBilin Ω u v :=
  (Op.gardingForm Ω).inner_opA u v

/-- Riesz identity: `⟪opT Ω u, v⟫ = zerothForm Ω u v = ⟨u₀, v₀⟩_{L²}`. -/
lemma inner_opT (u v : H01 Ω) : ⟪opT Ω u, v⟫ = zerothForm Ω u v :=
  continuousLinearMapOfBilin_apply (zerothForm Ω) u v

/-- Riesz identity: `⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v`. -/
lemma inner_opE (u v : H01 Ω) :
    ⟪Op.opE Ω u, v⟫ = Op.shiftedBilin Ω Op.gardingγ u v :=
  (Op.gardingForm Ω).inner_opE u v

/-! ### Reduction to `1 - opK` -/

/-- `opA = opE - γ·opT`: subtracting the shift recovers the unshifted form. -/
lemma opA_eq :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω) - Op.gardingγ • opT Ω :=
  (Op.gardingForm Ω).opA_eq

/-- `opA = opE ∘ (1 - opK)`: the weak problem `Lu = f` becomes `(1 - opK)u = opE⁻¹(opA⁻¹…)`. -/
lemma opA_factor :
    Op.opA Ω = (Op.opE Ω : H01 Ω →L[ℝ] H01 Ω).comp (1 - Op.opK Ω) :=
  (Op.gardingForm Ω).opA_factor

/-- The weak problem `B[u, ·] = f` is the equation `opA u = g` for the Riesz representative `g`
of `f`. -/
lemma opA_eq_toDual_symm_iff (f : H01 Ω →L[ℝ] ℝ) (u : H01 Ω) :
    Op.opA Ω u = (InnerProductSpace.toDual ℝ (H01 Ω)).symm f
      ↔ ∀ v : H01 Ω, Op.fullBilin Ω u v = f v :=
  (Op.gardingForm Ω).opA_eq_toDual_symm_iff f u

end FullEllipticOp

end EllipticPdes.Sobolev
