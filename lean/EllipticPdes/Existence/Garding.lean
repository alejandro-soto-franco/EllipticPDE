/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Existence.DivFormExistence
public import EllipticPdes.Existence.FullOp
public import EllipticPdes.Form.DivFormEuclidean
public import EllipticPdes.Form.DivFormGarding
public import EllipticPdes.Form.GeneralForm
public import EllipticPdes.Poincare.BoxSlice
public import EllipticPdes.Poincare.BoundedDomain

/-!
# Transport, zeroth-order term, the Gårding inequality, and shifted existence

We add to the principal part `B_A` of `GeneralForm.lean` a **transport** term `bᵢ Dᵢu` and a
**zeroth-order** term `c u` (both bounded measurable, `c` not assumed signed):

  `B[U, V] = ∑ᵢⱼ ⟪aᵢⱼ ∂ᵢu, ∂ⱼv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v₀⟫ + ⟪c u₀, v₀⟫`.

This is Evans §6.1.1's full divergence-form operator `Lu = -Dⱼ(aᵢⱼDᵢu) + bᵢDᵢu + cu`.

* **Gårding inequality** (`FullEllipticOp.garding`, Evans §6.2.2, Theorem 2(ii)): there
  are `β > 0`, `γ ≥ 0` with `β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for all `U ∈ H₀¹(Ω)`.
  We take `β = λ/2` and `γ = λ/2 + ‖c‖∞ + d ‖b‖∞² / (2λ)`. The transport term is absorbed
  into the ellipticity gap by the Peter-Paul (Young) inequality.
* **Shifted existence** (`FullEllipticOp.weak_solution`, Evans §6.2.2, Theorem 3): for
  any shift
  `μ ≥ γ` the shifted form `B_μ[U, V] = B[U, V] + μ ⟪u₀, v₀⟫` is coercive (Gårding already
  controls the full `H¹` norm, so **no Poincaré inequality is needed** here), and Lax-Milgram
  yields a unique weak solution `u ∈ H₀¹(Ω)` of `Lu + μu = f` for every `f ∈ H⁻¹(Ω)`.

The `γ = 0` symmetric case (no transport, `c ≥ 0`, needing Poincaré) is the separate
`EllipticCoeff.bilin_coercive` of `GeneralForm.lean`.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Sobolev

variable {d : ℕ}

/-- The Peter-Paul (Young) inequality `B x y ≤ (λ/2) x² + (B²/2λ) y²` for `λ > 0`. -/
lemma young_peterPaul {lam B x y : ℝ} (hlam : 0 < lam) :
    B * x * y ≤ lam / 2 * x ^ 2 + B ^ 2 / (2 * lam) * y ^ 2 :=
  DivForm.young_peterPaul hlam

namespace FullEllipticOp

variable (Op : FullEllipticOp d)

/-- **Gårding inequality** (Evans §6.2.2, Theorem 2(ii)). With `β = λ/2` and `γ` the
shift constant, `β ‖U‖²_{H¹} ≤ B[U, U] + γ ‖u₀‖²_{L²}` for every `U ∈ H₀¹(Ω)`. -/
theorem garding (Ω : Set (EuclideanSpace ℝ (Fin d))) (U : H01 Ω) :
    Op.lam / 2 * ‖U‖ ^ 2
      ≤ Op.fullBilin Ω U U + Op.gardingγ * ‖(U : H1amb Ω) 0‖ ^ 2 := by
  have h := (DivForm.FullEllipticOp.ofCoord Op).garding Ω (H1Graph.h01Equiv Ω U)
  rwa [LinearIsometryEquiv.norm_map, DivForm.FullEllipticOp.form_h01Equiv,
    DivForm.FullEllipticOp.gardingγ_ofCoord, H1Graph.fnL_h01Equiv] at h

/-! ### Shifted coercivity and existence (Evans §6.2.2, Theorem 3) -/
/-- **Shifted coercivity** (Evans §6.2.2, Theorem 3). For any shift `μ ≥ γ`, the shifted
form `B_μ` is
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

/-- **Existence and uniqueness for `Lu + μu = f`** (Evans §6.2.2, Theorem 3). For a
shift `μ ≥ γ` and
any continuous functional `f` on `H₀¹(Ω)`, there is a unique `u ∈ H₀¹(Ω)` solving the shifted
weak problem `B_μ[u, v] = f v` for all `v`. -/
theorem weak_solution (Ω : Set (EuclideanSpace ℝ (Fin d))) {μ : ℝ}
    (hμ : Op.gardingγ ≤ μ) (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, Op.shiftedBilin Ω μ u v = f v :=
  EllipticPdes.lax_milgram (Op.shiftedBilin_coercive Ω hμ) f

/-! ### Transport-free, nonnegative-zeroth coercive case (Evans §6.2.2, closing
Examples remark)
-/

/-- **Nonnegativity of the lower-order form** when the transport field vanishes (`b = 0`
a.e. on `Ω`) and the zeroth coefficient is nonnegative (`c ≥ 0` a.e. on `Ω`): the
transport terms `⟪bᵢ ∂ᵢu, u₀⟫` are zero and `⟪c u₀, u₀⟫ = ∫_Ω c u₀² ≥ 0`. -/
lemma lowerBilin_self_nonneg (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (U : H01 Ω) :
    0 ≤ Op.lowerBilin Ω U U := by
  rw [Op.lowerBilin_apply]
  have htrans : (∑ i : Fin d, ⟪Op.bAct i ((U : H1amb Ω) i.succ), ((U : H1amb Ω) 0)⟫) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    simp only [FullEllipticOp.bAct]
    rw [inner_mulCoeffL_eq]
    have hzero : ∀ᵐ x ∂(volume.restrict Ω),
        Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((U : H1amb Ω) 0 x : ℝ) = 0 :=
      (hb i).mono fun x hx => by rw [hx, zero_mul, zero_mul]
    calc (∫ x in Ω, Op.b x i * ((U : H1amb Ω) i.succ x : ℝ) * ((U : H1amb Ω) 0 x : ℝ))
        = ∫ _x in Ω, (0 : ℝ) := integral_congr_ae hzero
      _ = 0 := integral_zero _ _
  rw [htrans, zero_add]
  simp only [FullEllipticOp.cAct]
  rw [inner_mulCoeffL_eq]
  refine integral_nonneg_of_ae (hc.mono fun x hx => ?_)
  simp only [Pi.zero_apply]
  nlinarith [hx, sq_nonneg ((U : H1amb Ω) 0 x : ℝ)]

/-- **Quantitative coercivity for the transport-free, nonnegative-zeroth case**
(Evans §6.2.2, closing Examples remark). If the transport field vanishes (`b ≡ 0`) and
the zeroth coefficient is
nonnegative (`c ≥ 0`), the full divergence form `B = B_A + c` dominates the full `H¹`
norm with the explicit constant `λ / (C_P + 1)`: the zeroth term only helps, ellipticity
controls the gradient, and the Poincaré inequality lifts that to the full `H¹` norm.
This is the constant-level form of [`fullBilin_coercive_of_nonneg_zeroth`]; the explicit
constant feeds the Lax-Milgram a-priori estimate. -/
theorem fullBilin_coercive_const_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : HasTestPoincare Ω CP) (U : H01 Ω) :
    Op.lam / (CP + 1) * ‖U‖ * ‖U‖ ≤ Op.fullBilin Ω U U := by
  have hpos : (0 : ℝ) < CP + 1 := by linarith
  have hne : (CP : ℝ) + 1 ≠ 0 := hpos.ne'
  set S : ℝ := ∑ i : Fin d, ‖(U : H1amb Ω) i.succ‖ ^ 2 with hS
  have hA : Op.lam * S ≤ Op.toEllipticCoeff.bilin Ω U U := Op.toEllipticCoeff.bilin_self_ge U
  have hlow : 0 ≤ Op.lowerBilin Ω U U := Op.lowerBilin_self_nonneg Ω hb hc U
  have hBUU : Op.lam * S ≤ Op.fullBilin Ω U U := by
    rw [Op.fullBilin_apply]; linarith
  have hnorm : ‖U‖ ^ 2 = ‖(U : H1amb Ω) 0‖ ^ 2 + S := by
    rw [show ‖U‖ = ‖(U : H1amb Ω)‖ from rfl, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
  have hpoin : ‖(U : H1amb Ω) 0‖ ^ 2 ≤ CP * S :=
    EllipticPdes.Poincare.poincare_H01 CP hbase U.2
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hkey : ‖U‖ * ‖U‖ ≤ (CP + 1) * S := by
    have : ‖U‖ ^ 2 ≤ (CP + 1) * S := by rw [hnorm]; nlinarith [hpoin]
    nlinarith [this]
  rw [mul_assoc]
  calc Op.lam / (CP + 1) * (‖U‖ * ‖U‖)
      ≤ Op.lam / (CP + 1) * ((CP + 1) * S) :=
        mul_le_mul_of_nonneg_left hkey (div_pos Op.lam_pos hpos).le
    _ = Op.lam * S := by field_simp
    _ ≤ Op.fullBilin Ω U U := hBUU

/-- **Coercivity for the transport-free, nonnegative-zeroth case** (Evans §6.2.2,
closing Examples remark). If the
transport field vanishes (`b ≡ 0`) and the zeroth coefficient is nonnegative (`c ≥ 0`), the
full divergence form `B = B_A + c` is coercive on `H₀¹(Ω)` *without a spectral shift*: the
zeroth term only helps, ellipticity controls the gradient, and the Poincaré inequality lifts
that to the full `H¹` norm (the `γ = 0` Gårding case, with constant `λ / (C_P + 1)`). -/
theorem fullBilin_coercive_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2) :
    IsCoercive (Op.fullBilin Ω) :=
  ⟨Op.lam / (CP + 1), div_pos Op.lam_pos (by linarith),
    Op.fullBilin_coercive_const_of_nonneg_zeroth Ω hb hc CP hCP hbase⟩

/-- **Existence, uniqueness and a-priori bound for the transport-free, nonnegative-zeroth
operator** (the `γ = 0` specialisation of Evans's First Existence Theorem, §6.2.2). With
`b ≡ 0`, `c ≥ 0`, and the test-function Poincaré bound, the full divergence form `B = B_A + c`
is coercive with no spectral shift, so Lax-Milgram yields for every continuous functional `f`
on `H₀¹(Ω)` a unique weak solution `u` of `Lu = f`, with `‖u‖_{H₀¹} ≤ (C_P + 1) / λ · ‖f‖`,
the reciprocal of the coercivity constant `λ / (C_P + 1)`. -/
theorem weak_solution_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) {CP : ℝ} (hCP : 0 ≤ CP)
    (hbase : HasTestPoincare Ω CP) (f : H01 Ω →L[ℝ] ℝ) :
    (∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) ∧
      ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = f v) →
        ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  have hco := Op.fullBilin_coercive_const_of_nonneg_zeroth Ω hb hc CP hCP hbase
  have hα : 0 < Op.lam / (CP + 1) := div_pos Op.lam_pos (by linarith)
  refine ⟨EllipticPdes.lax_milgram ⟨_, hα, hco⟩ f, fun u hu => ?_⟩
  simpa [inv_div] using norm_weak_solution_le hα hco hu

/-- **`L²` right-hand side.** Under the hypotheses of `weak_solution_of_nonneg_zeroth`, every
`f ∈ L²(Ω)`, entering through the pairing `⟨f, v⟩ = ∫_Ω f · v₀` (the embedding
`L²(Ω) ⊆ H⁻¹(Ω)`, [`l2Functional`]), has a unique weak solution `u ∈ H₀¹(Ω)` of
`B[u, v] = ⟨f, v⟩`, and every weak solution obeys `‖u‖_{H₀¹} ≤ (C_P + 1) / λ · ‖f‖_{L²}`. -/
theorem weak_solution_L2_of_nonneg_zeroth (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) {CP : ℝ} (hCP : 0 ≤ CP)
    (hbase : HasTestPoincare Ω CP) (f : L2D Ω) :
    (∃! u : H01 Ω, ∀ v : H01 Ω,
      Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) ∧
    ∀ u : H01 Ω, (∀ v : H01 Ω,
        Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖ := by
  have h := Op.weak_solution_of_nonneg_zeroth Ω hb hc hCP hbase (l2Functional Ω f)
  simp only [l2Functional_eq_integral] at h
  refine ⟨h.1, fun u hu => (h.2 u hu).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (norm_l2Functional_le _ f)
    (div_nonneg (by linarith) Op.lam_pos.le)

/-- **Existence, uniqueness and the a-priori bound on any domain inside a coordinate box,
`H⁻¹` right-hand side.** For `Lu = -Dⱼ(aᵢⱼ Dᵢu) + cu` with `c ≥ 0` on a domain `Ω` contained
in the open box `∏ₖ (aₖ, bₖ)`, the test-function Poincaré hypothesis follows from
[`Poincare.testfn_bound_of_subset_euclBox`] with side contributions `(bᵢ - aᵢ)² / 2 ≤ C`. Every
continuous functional `f` on `H₀¹(Ω)` admits a unique weak solution, obeying the Lax-Milgram
estimate with coercivity constant `α = λ / (C / (n + 1) + 1)`. -/
theorem weak_solution_of_nonneg_zeroth_of_subset_euclBox {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (hsub : Ω ⊆ Poincare.euclBox a b)
    (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (f : H01 Ω →L[ℝ] ℝ) :
    (∃! u : H01 Ω, ∀ v : H01 Ω, Op.fullBilin Ω u v = f v) ∧
      ∀ u : H01 Ω, (∀ v : H01 Ω, Op.fullBilin Ω u v = f v) →
        ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ :=
  Op.weak_solution_of_nonneg_zeroth Ω hb hc
    (div_nonneg (le_trans (by positivity) (hC 0)) (by positivity))
    (fun h => Poincare.testfn_bound_of_subset_euclBox hab hsub hC h) f

/-- **`L²` right-hand-side instance on any domain inside a coordinate box.** For
`f ∈ L²(Ω)` the weak problem `B[u, v] = ∫_Ω f · v₀` has a unique solution with
`‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖_{L²}`, `α = λ / (C / (n + 1) + 1)`. -/
theorem weak_solution_L2_of_nonneg_zeroth_of_subset_euclBox {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (a b : Fin (n + 1) → ℝ) (hab : ∀ k, a k ≤ b k) (hsub : Ω ⊆ Poincare.euclBox a b)
    (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) (f : L2D Ω) :
    (∃! u : H01 Ω, ∀ v : H01 Ω,
      Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) ∧
    ∀ u : H01 Ω, (∀ v : H01 Ω,
        Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
      ‖u‖ ≤ (C / (n + 1) + 1) / Op.lam * ‖f‖ :=
  Op.weak_solution_L2_of_nonneg_zeroth Ω hb hc
    (div_nonneg (le_trans (by positivity) (hC 0)) (by positivity))
    (fun h => Poincare.testfn_bound_of_subset_euclBox hab hsub hC h) f

/-- **Existence, uniqueness and the a-priori bound on an arbitrary bounded domain, `L²`
right-hand side.** The Poincaré constant `CP` is supplied by `poincare_H01_of_bounded` and is
quantified before the datum, so it depends only on `Ω`; every `f ∈ L²(Ω)` then obeys
`‖u‖_{H₀¹} ≤ (CP + 1)/λ · ‖f‖_{L²}`. -/
theorem weak_solution_L2_of_nonneg_zeroth_of_bounded {n : ℕ}
    (Op : FullEllipticOp (n + 1)) {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩb : Bornology.IsBounded Ω)
    (hb : ∀ i, ∀ᵐ x ∂(volume.restrict Ω), Op.b x i = 0)
    (hc : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ Op.c x) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f : L2D Ω,
      ((∃! u : H01 Ω, ∀ v : H01 Ω,
        Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ))
      ∧ ∀ u : H01 Ω,
          (∀ v : H01 Ω,
            Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ)) →
            ‖u‖ ≤ (CP + 1) / Op.lam * ‖f‖) := by
  have hb' : ∀ᵐ x ∂(volume.restrict Ω), (DivForm.FullEllipticOp.ofCoord Op).b x = 0 := by
    filter_upwards [ae_all_iff.2 hb] with x hx
    ext i
    simp [DivForm.FullEllipticOp.ofCoord, hx i]
  obtain ⟨CP, hCP, h⟩ :=
    (DivForm.FullEllipticOp.ofCoord Op).weak_solution_of_nonneg_zeroth_of_bounded hΩb hb' hc
  refine ⟨CP, hCP, fun f => ?_⟩
  obtain ⟨h1, h2⟩ := h f
  have hpair (v : H01 Ω) : ⟪f, H1Graph.embL2 volume Ω (H1Graph.h01Equiv Ω v)⟫
      = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) := by
    rw [H1Graph.embL2_h01Equiv, L2.inner_def]
    simp [mul_comm]
  have hiff (u : H01 Ω) : (∀ v : H1Graph.H01 volume Ω,
        (DivForm.FullEllipticOp.ofCoord Op).formOn Ω _ (H1Graph.h01Equiv Ω u) v =
          ⟪f, H1Graph.embL2 volume Ω v⟫) ↔
      ∀ v : H01 Ω, Op.fullBilin Ω u v = ∫ x in Ω, (f x : ℝ) * ((v : H1amb Ω) 0 x : ℝ) := by
    refine ⟨fun hu v => ?_, fun hu v => ?_⟩
    · rw [← hpair, ← hu (H1Graph.h01Equiv Ω v), DivForm.FullEllipticOp.form_h01Equiv]
    · rw [← (H1Graph.h01Equiv Ω).apply_symm_apply v]
      exact (DivForm.FullEllipticOp.form_h01Equiv Op Ω u _).trans
        ((hu _).trans (hpair _).symm)
  refine ⟨?_, fun u hu => ?_⟩
  · simp only [← hiff]
    exact ((H1Graph.h01Equiv Ω).symm.toEquiv.existsUnique_congr_left.trans (by simp)).mp h1
  · have := h2 _ ((hiff u).2 hu)
    rwa [LinearIsometryEquiv.norm_map] at this

end FullEllipticOp

end EllipticPdes.Sobolev
