/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Form.GeneralForm

/-!
# The coordinate full divergence-form operator

The coordinate operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu` on `H₀¹(Ω) ⊆ H1amb Ω`: the structure
`FullEllipticOp d`, its transport and zeroth-order actions on `L²(Ω)`, the bounded bilinear
forms `lowerBilin`, `fullBilin`, `zerothForm`, `shiftedBilin`, and the Gårding shift constant
`gardingγ`. The Gårding inequality and the existence theorems are in `Existence.Garding`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The `i`-th coordinate `U ↦ Uᵢ` of an element of `H₀¹(Ω) ⊆ H1amb Ω`, as a continuous linear map
into `L²(Ω)`: the `PiLp` projection precomposed with the submodule inclusion. -/
def coordL (Ω : Set (EuclideanSpace ℝ (Fin d))) (i : Fin (d + 1)) : H01 Ω →L[ℝ] L2D Ω :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D Ω) i).comp (H01 Ω).subtypeL

/-- Simp lemma: `coordL Ω i U` is the `i`-th coordinate of `U`. -/
@[simp] lemma coordL_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (i : Fin (d + 1)) (U : H01 Ω) :
    coordL Ω i U = (U : H1amb Ω) i := rfl

/-- The test-function Poincaré bound on `Ω` with constant `CP`: for every test function `φ`
of `Ω`, `‖φ‖²_{L²} ≤ CP ∑ᵢ ‖∂ᵢφ‖²_{L²}`. -/
def HasTestPoincare (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) : Prop :=
  ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
    ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2

/-! ### Full divergence-form operator -/

/-- A full second-order divergence-form operator: a uniformly elliptic principal part `A`
together with a bounded measurable transport field `b` and zeroth-order coefficient `c`. -/
structure FullEllipticOp (d : ℕ) extends EllipticCoeff d where
  /-- Transport (first-order) coefficients. -/
  b : EuclideanSpace ℝ (Fin d) → Fin d → ℝ
  /-- Zeroth-order coefficient. -/
  c : EuclideanSpace ℝ (Fin d) → ℝ
  /-- Sup bound on the transport field. -/
  Bsup : ℝ
  /-- Sup bound on the zeroth-order coefficient. -/
  Csup : ℝ
  /-- The bound on the transport field is nonnegative. -/
  Bsup_nonneg : 0 ≤ Bsup
  /-- The bound on the zeroth-order coefficient is nonnegative. -/
  Csup_nonneg : 0 ≤ Csup
  /-- Every component of the transport field is measurable. -/
  b_meas : ∀ i, Measurable (fun x => b x i)
  /-- The zeroth-order coefficient is measurable. -/
  c_meas : Measurable c
  /-- Every component of the transport field is bounded by `Bsup` almost everywhere. -/
  b_bdd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |b x i| ≤ Bsup
  /-- The zeroth-order coefficient is bounded by `Csup` almost everywhere. -/
  c_bdd : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Csup

namespace FullEllipticOp

variable (Op : FullEllipticOp d)

/-- The transport coefficient `bᵢ` acting on `L²(Ω)`. -/
def bAct {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (Op.b_meas i) (ae_restrict_of_ae (Op.b_bdd i))

/-- The zeroth-order coefficient `c` acting on `L²(Ω)`. -/
def cAct {Ω : Set (EuclideanSpace ℝ (Fin d))} : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL Op.c_meas (ae_restrict_of_ae Op.c_bdd)

/-- Operator-norm bound for the transport action: `‖Op.bAct i g‖ ≤ Bsup · ‖g‖`. -/
lemma norm_bAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) (g : L2D Ω) :
    ‖Op.bAct i g‖ ≤ Op.Bsup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-- Operator-norm bound for the zeroth-order action: `‖Op.cAct g‖ ≤ Csup · ‖g‖`. -/
lemma norm_cAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (g : L2D Ω) :
    ‖Op.cAct g‖ ≤ Op.Csup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-! ### Lower-order (transport + zeroth) bilinear form -/

/-- The lower-order part `∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫` as a bounded bilinear form. -/
def lowerBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (∑ i : Fin d, (innerSL ℝ).bilinearComp ((Op.bAct i).comp (coordL Ω i.succ)) (coordL Ω 0))
    + (innerSL ℝ).bilinearComp (Op.cAct.comp (coordL Ω 0)) (coordL Ω 0)

/-- Simp lemma: unfolds `lowerBilin Ω U V` to the transport and zeroth-order inner products. -/
@[simp] lemma lowerBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.lowerBilin Ω U V
      = (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
        + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫ := by
  simp [FullEllipticOp.lowerBilin, _root_.sum_apply]

/-- The full divergence-form bilinear form `B = B_A + (transport + zeroth)`. -/
def fullBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.toEllipticCoeff.bilin Ω + Op.lowerBilin Ω

/-- `fullBilin = B_A + lowerBilin`: principal part plus transport and zeroth-order. -/
lemma fullBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.fullBilin Ω U V = Op.toEllipticCoeff.bilin Ω U V + Op.lowerBilin Ω U V := by
  simp only [FullEllipticOp.fullBilin, _root_.add_apply]

/-! ### Gårding inequality -/

/-- The Gårding shift constant `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. -/
def gardingγ : ℝ :=
  Op.lam / 2 + Op.Csup + (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam)

/-- The Gårding shift constant `γ` is non-negative. -/
lemma gardingγ_nonneg : 0 ≤ Op.gardingγ := by
  have : (0 : ℝ) < 2 * Op.lam := by have := Op.lam_pos; linarith
  unfold gardingγ
  have h1 : (0 : ℝ) ≤ Op.lam / 2 := by have := Op.lam_pos; linarith
  have h2 : (0 : ℝ) ≤ (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) :=
    div_nonneg (by positivity) this.le
  linarith [Op.Csup_nonneg]

/-- The Gårding shift constant `γ` is strictly positive. -/
lemma gardingγ_pos : 0 < Op.gardingγ := by
  have h1 := Op.lam_pos
  have h2 := Op.Csup_nonneg
  have h3 : (0 : ℝ) ≤ (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) :=
    div_nonneg (by positivity) (by linarith)
  unfold gardingγ
  linarith


/-- The zeroth `L²` form `⟪u₀, v₀⟫` on `H₀¹(Ω)`, used for the spectral shift. -/
def zerothForm (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (coordL Ω 0) (coordL Ω 0)

/-- Simp lemma: `zerothForm Ω U V = ⟪(U : H1amb Ω) 0, (V : H1amb Ω) 0⟫`. -/
@[simp] lemma zerothForm_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    zerothForm Ω U V = ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ :=
  rfl

/-- The shifted bilinear form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` associated to `Lu + μu`. -/
def shiftedBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.fullBilin Ω + μ • zerothForm Ω

/-- `shiftedBilin Ω μ U V = fullBilin Ω U V + μ · ⟪u₀, v₀⟫`. -/
lemma shiftedBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (U V : H01 Ω) :
    Op.shiftedBilin Ω μ U V = Op.fullBilin Ω U V + μ * ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.shiftedBilin, _root_.add_apply,
    _root_.smul_apply, zerothForm_apply, smul_eq_mul]

end FullEllipticOp

end EllipticPdes.Sobolev
