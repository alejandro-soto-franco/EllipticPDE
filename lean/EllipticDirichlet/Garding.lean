import EllipticDirichlet.GeneralForm

/-!
# Transport, zeroth-order term, the Gårding inequality, and shifted existence

We add to the principal part `B_A` of `GeneralForm.lean` a **transport** term `bᵢ Dᵢu` and a
**zeroth-order** term `c u` (both bounded measurable, `c` not assumed signed):

  `B[U, V] = ∑ᵢⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫`.

This is Guo §VII.1.1's full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu`.

* **Gårding inequality** (`FullEllipticOp.garding`, Guo §VII.2.5(ii)): there are `β > 0`,
  `γ ≥ 0` with `β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for all `U ∈ H₀¹(Ω)`. We take
  `β = λ/2` and `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. The transport term is absorbed into the
  ellipticity gap by the Peter-Paul (Young) inequality.
* **Shifted existence** (`FullEllipticOp.weak_solution`, Guo §VII.3.3): for any shift
  `μ ≥ γ` the shifted form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` is coercive (Gårding already
  controls the full `H¹` norm, so **no Poincaré inequality is needed** here), and Lax-Milgram
  yields a unique weak solution `u ∈ H₀¹(Ω)` of `Lu + μu = f` for every `f ∈ H⁻¹(Ω)`.

The `γ = 0` symmetric case (no transport, `c ≥ 0`, needing Poincaré) is the separate
`EllipticCoeff.bilin_coercive` of `GeneralForm.lean`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticDirichlet.Sobolev

variable {d : ℕ}

/-- The Peter-Paul (Young) inequality `B x y ≤ (λ/2) x² + (B²/2λ) y²` for `λ > 0`. -/
lemma young_peterPaul {lam B x y : ℝ} (hlam : 0 < lam) :
    B * x * y ≤ lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 := by
  have hl : lam ≠ 0 := hlam.ne'
  have h2l : (0 : ℝ) < 2 * lam := by linarith
  rw [← sub_nonneg]
  have key : lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 - B * x * y
      = (lam * x - B * y) ^ 2 / (2 * lam) := by field_simp; ring
  rw [key]
  exact div_nonneg (sq_nonneg _) h2l.le

/-! ### The full divergence-form operator -/

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
  Bsup_nonneg : 0 ≤ Bsup
  Csup_nonneg : 0 ≤ Csup
  b_meas : ∀ i, Measurable (fun x => b x i)
  c_meas : Measurable c
  b_bdd : ∀ x i, |b x i| ≤ Bsup
  c_bdd : ∀ x, |c x| ≤ Csup

namespace FullEllipticOp

variable (Op : FullEllipticOp d)

/-- The transport coefficient `bᵢ` acting on `L²(Ω)`. -/
def bAct {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL (Op.b_meas i) (fun x => Op.b_bdd x i)

/-- The zeroth-order coefficient `c` acting on `L²(Ω)`. -/
def cAct {Ω : Set (EuclideanSpace ℝ (Fin d))} : L2D Ω →L[ℝ] L2D Ω :=
  mulCoeffL Op.c_meas (fun x => Op.c_bdd x)

lemma norm_bAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (i : Fin d) (g : L2D Ω) :
    ‖Op.bAct i g‖ ≤ Op.Bsup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

lemma norm_cAct_le {Ω : Set (EuclideanSpace ℝ (Fin d))} (g : L2D Ω) :
    ‖Op.cAct g‖ ≤ Op.Csup * ‖g‖ :=
  norm_mulCoeffL_le _ _ g

/-! ### The lower-order (transport + zeroth) bilinear form -/

/-- The lower-order part `∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫` as a bare bilinear map. -/
def lowerBilinₗ (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →ₗ[ℝ] (H01 Ω) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun U V => (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
      + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, map_add,
          inner_add_left, Finset.sum_add_distrib]; ring)
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, map_smul,
          real_inner_smul_left, smul_eq_mul, mul_add, Finset.mul_sum])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply,
          inner_add_right, Finset.sum_add_distrib]; ring)
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply,
          real_inner_smul_right, smul_eq_mul, mul_add, Finset.mul_sum])

/-- The lower-order bilinear form as a bounded form, with norm bound `d·Bsup + Csup`. -/
def lowerBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (Op.lowerBilinₗ Ω).mkContinuous₂ ((d : ℝ) * Op.Bsup + Op.Csup) (by
    intro U V
    simp only [FullEllipticOp.lowerBilinₗ, LinearMap.mk₂_apply]
    have hb : ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
        ≤ (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ := by
      calc ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
          ≤ ∑ i : Fin d, ‖⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : Fin d, Op.Bsup * ‖U‖ * ‖V‖ := by
            apply Finset.sum_le_sum; intro i _
            calc ‖⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
                ≤ ‖Op.bAct i ((U : H1amb Ω) i.succ)‖ * ‖(V : H1amb Ω) 0‖ :=
                  norm_inner_le_norm _ _
              _ ≤ (Op.Bsup * ‖U‖) * ‖V‖ :=
                  mul_le_mul (le_trans (Op.norm_bAct_le i _)
                    (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) Op.Bsup_nonneg))
                    (PiLp.norm_apply_le _ _) (norm_nonneg _)
                    (mul_nonneg Op.Bsup_nonneg (norm_nonneg _))
        _ = (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hc : ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖ ≤ Op.Csup * ‖U‖ * ‖V‖ :=
      calc ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖
          ≤ ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(V : H1amb Ω) 0‖ := norm_inner_le_norm _ _
        _ ≤ (Op.Csup * ‖U‖) * ‖V‖ :=
            mul_le_mul (le_trans (Op.norm_cAct_le _)
              (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) Op.Csup_nonneg))
              (PiLp.norm_apply_le _ _) (norm_nonneg _)
              (mul_nonneg Op.Csup_nonneg (norm_nonneg _))
    calc ‖(∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
            + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖
        ≤ ‖∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫‖
            + ‖⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫‖ := norm_add_le _ _
      _ ≤ (d : ℝ) * Op.Bsup * ‖U‖ * ‖V‖ + Op.Csup * ‖U‖ * ‖V‖ := add_le_add hb hc
      _ = ((d : ℝ) * Op.Bsup + Op.Csup) * ‖U‖ * ‖V‖ := by ring)

@[simp] lemma lowerBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.lowerBilin Ω U V
      = (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((V : H1amb Ω) 0)⟫)
        + ⟪Op.cAct ((U : H1amb Ω) 0), ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.lowerBilin, LinearMap.mkContinuous₂_apply,
    FullEllipticOp.lowerBilinₗ, LinearMap.mk₂_apply]

/-- The full divergence-form bilinear form `B = B_A + (transport + zeroth)`. -/
def fullBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.toEllipticCoeff.bilin Ω + Op.lowerBilin Ω

lemma fullBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    Op.fullBilin Ω U V = Op.toEllipticCoeff.bilin Ω U V + Op.lowerBilin Ω U V := by
  simp only [FullEllipticOp.fullBilin, ContinuousLinearMap.add_apply]

/-! ### The Gårding inequality -/

/-- The Gårding shift constant `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. -/
def gardingγ : ℝ :=
  Op.lam / 2 + Op.Csup + (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam)

lemma gardingγ_nonneg : 0 ≤ Op.gardingγ := by
  have : (0 : ℝ) < 2 * Op.lam := by have := Op.lam_pos; linarith
  unfold gardingγ
  have h1 : (0 : ℝ) ≤ Op.lam / 2 := by have := Op.lam_pos; linarith
  have h2 : (0 : ℝ) ≤ (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) :=
    div_nonneg (by positivity) this.le
  linarith [Op.Csup_nonneg]

/-- **The Gårding inequality** (Guo §VII.2.5(ii)). With `β = λ/2` and `γ = gardingγ`,
`β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for every `U ∈ H₀¹(Ω)`. -/
theorem garding (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    Op.lam / 2 * ‖U‖ ^ 2
      ≤ Op.fullBilin Ω U U + Op.gardingγ * ‖(U : H1amb Ω) 0‖ ^ 2 := by
  set n0 : ℝ := ‖(U : H1amb Ω) 0‖ ^ 2 with hn0
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  set K : ℝ := (d : ℝ) * Op.Bsup ^ 2 / (2 * Op.lam) with hK
  -- principal-part lower bound from ellipticity
  have hA : Op.lam * S ≤ Op.toEllipticCoeff.bilin Ω U U := Op.toEllipticCoeff.bilin_self_ge U
  -- per-term Cauchy-Schwarz + Peter-Paul, written sign-free to avoid a sum-of-negations
  have hbound : ∀ i : Fin d, (0 : ℝ)
      ≤ (Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0)
        + ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
    intro i
    have hcs : -⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫
        ≤ Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0 := by
      calc -⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫
          ≤ |⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫| := neg_le_abs _
        _ ≤ ‖Op.bAct i ((U : H1amb Ω) i.succ)‖ * ‖(U : H1amb Ω) 0‖ := abs_real_inner_le_norm _ _
        _ ≤ Op.Bsup * ‖(U : H1amb Ω) i.succ‖ * ‖(U : H1amb Ω) 0‖ := by
            gcongr; exact Op.norm_bAct_le i _
        _ ≤ Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2 + Op.Bsup ^ 2 / (2 * Op.lam) * n0 := by
            rw [hn0]; exact young_peterPaul Op.lam_pos
    linarith [hcs]
  -- transport lower bound: `∑ ⟪bᵢ ∂ᵢu, u₀⟫ ≥ -(λ/2 S + K n0)`
  have hT : (0 : ℝ) ≤ (Op.lam / 2 * S + K * n0)
      + ∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
    calc (0 : ℝ) = ∑ _i : Fin d, (0 : ℝ) := by rw [Finset.sum_const_zero]
      _ ≤ ∑ i : Fin d, ((Op.lam / 2 * ‖(U : H1amb Ω) i.succ‖ ^ 2
            + Op.Bsup ^ 2 / (2 * Op.lam) * n0)
            + ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫) :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = (Op.lam / 2 * S + K * n0)
            + ∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hK, hS]
          ring
  -- zeroth-order lower bound (|c| ≤ Csup, no sign assumed)
  have hC : -(Op.Csup * n0) ≤ ⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫ := by
    rw [neg_le]
    calc -⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫
        ≤ |⟪Op.cAct ((U : H1amb Ω) 0), ((U : H1amb Ω) 0)⟫| := neg_le_abs _
      _ ≤ ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(U : H1amb Ω) 0‖ := abs_real_inner_le_norm _ _
      _ ≤ Op.Csup * n0 := by
          rw [hn0]
          calc ‖Op.cAct ((U : H1amb Ω) 0)‖ * ‖(U : H1amb Ω) 0‖
              ≤ (Op.Csup * ‖(U : H1amb Ω) 0‖) * ‖(U : H1amb Ω) 0‖ :=
                mul_le_mul_of_nonneg_right (Op.norm_cAct_le _) (norm_nonneg _)
            _ = Op.Csup * ‖(U : H1amb Ω) 0‖ ^ 2 := by ring
  -- the H¹ norm splits as n0 + S
  have hnorm : ‖U‖ ^ 2 = n0 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, hn0, hS]
  rw [Op.fullBilin_apply, Op.lowerBilin_apply, gardingγ, ← hK, hnorm]
  linarith [hA, hT, hC]

/-! ### Shifted coercivity and existence (Guo §VII.3.3) -/

/-- The zeroth `L²` form `⟪u₀, v₀⟫` on `H₀¹(Ω)`, used for the spectral shift. -/
def zerothForm (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ (fun U V : H01 Ω => ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫)
    (by intro U₁ U₂ V; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_left])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_left,
          smul_eq_mul])
    (by intro U V₁ V₂; simp only [Submodule.coe_add, PiLp.add_apply, inner_add_right])
    (by intro c U V; simp only [Submodule.coe_smul, PiLp.smul_apply, real_inner_smul_right,
          smul_eq_mul])).mkContinuous₂ 1 (by
    intro U V
    simp only [LinearMap.mk₂_apply]
    calc ‖⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫‖
        ≤ ‖(U : H1amb Ω) 0‖ * ‖(V : H1amb Ω) 0‖ := norm_inner_le_norm _ _
      _ ≤ ‖U‖ * ‖V‖ := mul_le_mul (PiLp.norm_apply_le _ _) (PiLp.norm_apply_le _ _)
          (norm_nonneg _) (norm_nonneg _)
      _ = 1 * ‖U‖ * ‖V‖ := by ring)

@[simp] lemma zerothForm_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (U V : H01 Ω) :
    zerothForm Ω U V = ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.zerothForm, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]

/-- The shifted bilinear form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` associated to `Lu + μu`. -/
def shiftedBilin (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) :
    (H01 Ω) →L[ℝ] (H01 Ω) →L[ℝ] ℝ :=
  Op.fullBilin Ω + μ • zerothForm Ω

lemma shiftedBilin_apply (Ω : Set (EuclideanSpace ℝ (Fin d))) (μ : ℝ) (U V : H01 Ω) :
    Op.shiftedBilin Ω μ U V = Op.fullBilin Ω U V + μ * ⟪(U : H1amb Ω) 0, ((V : H1amb Ω) 0)⟫ := by
  simp only [FullEllipticOp.shiftedBilin, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, zerothForm_apply, smul_eq_mul]

/-- **Shifted coercivity** (Guo §VII.3.3). For any shift `μ ≥ γ`, the shifted form `B_μ` is
coercive with constant `λ/2`. The Gårding inequality already controls the full `H¹` norm,
so no Poincaré inequality is needed. -/
theorem shiftedBilin_coercive (Ω : Set (EuclideanSpace ℝ (Fin d))) {μ : ℝ}
    (hμ : Op.gardingγ ≤ μ) :
    IsCoercive (Op.shiftedBilin Ω μ) := by
  refine ⟨Op.lam / 2, by have := Op.lam_pos; linarith, ?_⟩
  intro U
  have hg := Op.garding Ω U
  have hn0 : (0 : ℝ) ≤ ‖(U : H1amb Ω) 0‖ ^ 2 := sq_nonneg _
  have hself : ⟪(U : H1amb Ω) 0, ((U : H1amb Ω) 0)⟫ = ‖(U : H1amb Ω) 0‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  rw [Op.shiftedBilin_apply, hself]
  have hμn : Op.gardingγ * ‖(U : H1amb Ω) 0‖ ^ 2 ≤ μ * ‖(U : H1amb Ω) 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hμ hn0
  have : Op.lam / 2 * ‖U‖ ^ 2 ≤ Op.fullBilin Ω U U + μ * ‖(U : H1amb Ω) 0‖ ^ 2 := by
    linarith [hg, hμn]
  calc Op.lam / 2 * ‖U‖ * ‖U‖ = Op.lam / 2 * ‖U‖ ^ 2 := by ring
    _ ≤ Op.fullBilin Ω U U + μ * ‖(U : H1amb Ω) 0‖ ^ 2 := this

/-- **Existence and uniqueness for `Lu + μu = f`** (Guo §VII.3.3). For a shift `μ ≥ γ` and
any continuous functional `f` on `H₀¹(Ω)`, there is a unique `u ∈ H₀¹(Ω)` solving the shifted
weak problem `B_μ[u, v] = f v` for all `v`. -/
theorem weak_solution (Ω : Set (EuclideanSpace ℝ (Fin d))) {μ : ℝ}
    (hμ : Op.gardingγ ≤ μ) (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.shiftedBilin Ω μ u v = f v := by
  have hco : IsCoercive (Op.shiftedBilin Ω μ) := Op.shiftedBilin_coercive Ω hμ
  have hgrep : ∀ w : H01 Ω,
      ⟪(InnerProductSpace.toDual ℝ (H01 Ω)).symm f, w⟫ = f w :=
    fun w => InnerProductSpace.toDual_symm_apply
  set g : H01 Ω := (InnerProductSpace.toDual ℝ (H01 Ω)).symm f with hg
  refine ⟨hco.continuousLinearEquivOfBilin.symm g, ?_, ?_⟩
  · intro v
    rw [← hco.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply, hgrep]
  · intro u hu
    apply hco.continuousLinearEquivOfBilin.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    refine ext_inner_right (𝕜 := ℝ) (fun w => ?_)
    rw [hco.continuousLinearEquivOfBilin_apply, hu w, ← hgrep w]

end FullEllipticOp

end EllipticDirichlet.Sobolev
