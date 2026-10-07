/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Campanato.Holder

/-!
# Campanato decay of a Hölder function

A function that is Hölder of exponent `α` on `Ω` oscillates by at most `K (2r)^α` over any ball
of radius `r` contained in `Ω`, so its mean oscillation there is bounded by `K (2r)^α` as well,
and squaring and integrating over a ball of volume `r^d |B(0,1)|` gives the Campanato bound with

  `M = K · 2^α · √|B(0,1)|`.

Together with `campanato_holderOnWith` this makes `CampanatoOn` a characterisation of Hölder
continuity, which is the form Schauder theory consumes: a Hölder coefficient feeds in a Campanato
decay rate, and a Campanato decay rate feeds out a Hölder bound.
-/

@[expose] public section

open MeasureTheory Set Metric Filter Module

open scoped NNReal ENNReal Topology

noncomputable section

namespace EllipticPdes.Campanato.Haar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

local notation "𝔡" => Module.finrank ℝ E

/-- A Hölder function stays within `K (2r)^α` of its mean over any ball of radius `r` inside the
set where the Hölder bound holds. -/
theorem abs_sub_ballAverage_le_of_holderOnWith {Ω : Set (E)}
    {u : E → ℝ} {α : ℝ} (hα : 0 < α) {K : ℝ≥0}
    (hu : HolderOnWith K (Real.toNNReal α) u Ω) {x : E} {r : ℝ}
    (hr : 0 < r) (hxr : Metric.ball x r ⊆ Ω) :
    ∀ y ∈ Metric.ball x r, |u y - ballAverage u x r| ≤ (K : ℝ) * (2 * r) ^ α := by
  have hαnn : ((Real.toNNReal α : ℝ≥0) : ℝ) = α := Real.coe_toNNReal α hα.le
  have hvol : volume.real (Metric.ball x r) = r ^ (𝔡 : ℝ) * unitBallVolume E :=
    measureReal_ball_rpow x hr
  have hvolpos : 0 < volume.real (Metric.ball x r) := by
    rw [hvol]
    exact mul_pos (Real.rpow_pos_of_pos hr (𝔡 : ℝ)) unitBallVolume_pos
  -- The Hölder bound between any two points of the ball.
  have hpair : ∀ z ∈ Metric.ball x r, ∀ w ∈ Metric.ball x r,
      |u z - u w| ≤ (K : ℝ) * (2 * r) ^ α := by
    intro z hz w hw
    have hd : dist z w ≤ 2 * r := by
      calc dist z w ≤ dist z x + dist x w := dist_triangle _ _ _
        _ ≤ r + r := by
            rw [dist_comm x w]
            exact add_le_add (le_of_lt (Metric.mem_ball.mp hz)) (le_of_lt (Metric.mem_ball.mp hw))
        _ = 2 * r := by ring
    have := hu.dist_le (hxr hz) (hxr hw)
    rw [Real.dist_eq, hαnn] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    exact Real.rpow_le_rpow dist_nonneg hd hα.le
  -- Continuity gives measurability, and the Hölder bound gives boundedness.
  have hcont : ContinuousOn u (Metric.ball x r) :=
    (hu.continuousOn (Real.toNNReal_pos.mpr hα)).mono hxr
  have hmeas : AEStronglyMeasurable u (volume.restrict (Metric.ball x r)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hxmem : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hint : IntegrableOn u (Metric.ball x r) volume := by
    refine ⟨hmeas, HasFiniteIntegral.of_bounded (C := |u x| + (K : ℝ) * (2 * r) ^ α) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hz' := hpair z hz x hxmem
    have hsplit := abs_sub_abs_le_abs_sub (u z) (u x)
    rw [Real.norm_eq_abs]
    linarith
  intro y hy
  have h1 : ∫ z in Metric.ball x r, (u y - u z)
      = volume.real (Metric.ball x r) * (u y - ballAverage u x r) := by
    rw [integral_sub (integrable_const _) hint, setIntegral_const, smul_eq_mul, ballAverage,
      setAverage_eq, smul_eq_mul]
    field_simp
  have h2 : |∫ z in Metric.ball x r, (u y - u z)|
      ≤ volume.real (Metric.ball x r) * ((K : ℝ) * (2 * r) ^ α) := by
    calc |∫ z in Metric.ball x r, (u y - u z)|
        ≤ ∫ z in Metric.ball x r, |u y - u z| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _z in Metric.ball x r, ((K : ℝ) * (2 * r) ^ α) := by
          refine setIntegral_mono_on ((integrable_const (u y)).sub hint).abs
            (integrable_const _) measurableSet_ball fun z hz => hpair y hy z hz
      _ = volume.real (Metric.ball x r) * ((K : ℝ) * (2 * r) ^ α) := by
          rw [setIntegral_const, smul_eq_mul]
  rw [h1, abs_mul, abs_of_pos hvolpos] at h2
  exact le_of_mul_le_mul_left h2 hvolpos

/-- **Converse of Campanato's characterisation.** A function that is Hölder of exponent `α`
with constant `K` on `Ω` satisfies the Campanato decay hypothesis on `Ω` with constant
`K · 2^α · √|B(0,1)|`. Squaring the mean-oscillation bound `K (2r)^α` and integrating over a ball
of volume `r^d |B(0,1)|` is the whole proof. -/
theorem campanatoOn_of_holderOnWith {Ω : Set (E)}
    {u : E → ℝ} {α : ℝ} (hα : 0 < α) {K : ℝ≥0}
    (hu : HolderOnWith K (Real.toNNReal α) u Ω) :
    CampanatoOn Ω u α ((K : ℝ) * 2 ^ α * Real.sqrt (unitBallVolume E)) := by
  have hω : (0 : ℝ) < unitBallVolume E := unitBallVolume_pos
  intro x r hr hxr
  have hosc := abs_sub_ballAverage_le_of_holderOnWith hα hu hr hxr
  have hvol : volume.real (Metric.ball x r) = r ^ (𝔡 : ℝ) * unitBallVolume E :=
    measureReal_ball_rpow x hr
  have hB : (0 : ℝ) ≤ (K : ℝ) * (2 * r) ^ α :=
    mul_nonneg K.coe_nonneg (Real.rpow_nonneg (by linarith) α)
  -- Pointwise the squared deviation is at most the square of the oscillation bound.
  have hpt : ∀ y ∈ Metric.ball x r,
      (u y - ballAverage u x r) ^ 2 ≤ ((K : ℝ) * (2 * r) ^ α) ^ 2 := by
    intro y hy
    have h := hosc y hy
    nlinarith [abs_nonneg (u y - ballAverage u x r), sq_abs (u y - ballAverage u x r)]
  have hintsq : IntegrableOn (fun y => (u y - ballAverage u x r) ^ 2)
      (Metric.ball x r) volume := by
    have hcont : ContinuousOn (fun y => (u y - ballAverage u x r) ^ 2) (Metric.ball x r) :=
      (((hu.continuousOn (Real.toNNReal_pos.mpr hα)).mono hxr).sub continuousOn_const).pow 2
    refine ⟨hcont.aestronglyMeasurable measurableSet_ball,
      HasFiniteIntegral.of_bounded (C := ((K : ℝ) * (2 * r) ^ α) ^ 2) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt y hy
  -- Integrate the pointwise bound over the ball.
  have hle : ∫ y in Metric.ball x r, (u y - ballAverage u x r) ^ 2
      ≤ (r ^ (𝔡 : ℝ) * unitBallVolume E) * ((K : ℝ) * (2 * r) ^ α) ^ 2 := by
    calc ∫ y in Metric.ball x r, (u y - ballAverage u x r) ^ 2
        ≤ ∫ _y in Metric.ball x r, ((K : ℝ) * (2 * r) ^ α) ^ 2 :=
          setIntegral_mono_on hintsq (integrable_const _) measurableSet_ball hpt
      _ = (r ^ (𝔡 : ℝ) * unitBallVolume E) * ((K : ℝ) * (2 * r) ^ α) ^ 2 := by
          rw [setIntegral_const, smul_eq_mul, hvol]
  refine hle.trans (le_of_eq ?_)
  -- The constants match: `(2r)^{2α} r^𝔡 |B(0,1)| = (K 2^α √|B(0,1)|)² r^{𝔡+2α} / K²`.
  have h2r : ((2 : ℝ) * r) ^ α = 2 ^ α * r ^ α := Real.mul_rpow (by norm_num) hr.le
  have hsplit : r ^ ((𝔡 : ℝ) + 2 * α) = r ^ (𝔡 : ℝ) * (r ^ α) ^ 2 := by
    have h2 : (r ^ α) ^ 2 = r ^ (2 * α) := by
      rw [← Real.rpow_natCast (r ^ α) 2, ← Real.rpow_mul hr.le]
      congr 1
      push_cast
      ring
    rw [Real.rpow_add hr, h2]
  have hsq : Real.sqrt (unitBallVolume E) ^ 2 = unitBallVolume E := Real.sq_sqrt hω.le
  rw [h2r, hsplit]
  calc r ^ (𝔡 : ℝ) * unitBallVolume E * ((K : ℝ) * (2 ^ α * r ^ α)) ^ 2
      = ((K : ℝ) * 2 ^ α) ^ 2 * (r ^ (𝔡 : ℝ) * (r ^ α) ^ 2) * unitBallVolume E := by ring
    _ = ((K : ℝ) * 2 ^ α) ^ 2 * (r ^ (𝔡 : ℝ) * (r ^ α) ^ 2)
          * Real.sqrt (unitBallVolume E) ^ 2 := by rw [hsq]
    _ = ((K : ℝ) * 2 ^ α * Real.sqrt (unitBallVolume E)) ^ 2
          * (r ^ (𝔡 : ℝ) * (r ^ α) ^ 2) := by ring

end EllipticPdes.Campanato.Haar

/-! ### Euclidean space -/

namespace EllipticPdes.Campanato

variable {d : ℕ}

/-- The volume of the unit ball of `EuclideanSpace ℝ (Fin d)`, as a real number. -/
def unitBallVolume (d : ℕ) : ℝ := Haar.unitBallVolume (EuclideanSpace ℝ (Fin d))

/-- **Campanato decay hypothesis** on Euclidean space. The mean oscillation of `u` over every
ball contained in `Ω` decays at the rate `r^{d + 2α}`, with constant `M`. -/
def CampanatoOn (Ω : Set (EuclideanSpace ℝ (Fin d))) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (α M : ℝ) : Prop :=
  Haar.CampanatoOn Ω u α M

/-- The Campanato limit on Euclidean space: the limit of the means over the balls
`B(x, 2^{-k})`. -/
def campanatoLimit (u : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Haar.campanatoLimit u x

/-- The Hölder constant Campanato's characterisation produces on Euclidean space. -/
def campanatoHolderConst (d : ℕ) (α : ℝ) : ℝ :=
  Haar.campanatoHolderConst (EuclideanSpace ℝ (Fin d)) α

/-- **Campanato's characterisation of Hölder continuity.** Let `u` be square integrable on the ball
`B(c, R)` and suppose its mean oscillation decays at the Campanato rate,

  `∫_{B(x,r)} |u - u_{x,r}|² ≤ M² r^{d + 2α}` for every ball `B(x, r) ⊆ B(c, R)`,

with `0 < α`. Then `campanatoLimit u` is a representative of `u` on every concentric ball
`B(c, ρ)` with `5ρ ≤ R`, and it is Hölder continuous there with exponent `α` and constant
`campanatoHolderConst d α · M`.

The factor `5` comes from the hypothesis: the pair estimate at `x, y ∈ B(c, ρ)` uses the balls
of radius `2 |x - y| < 4ρ` about both points, and those lie in `B(c, R)` exactly when `5ρ ≤ R`. -/
theorem campanato_holderOnWith (hd : 0 < d) {u : EuclideanSpace ℝ (Fin d) → ℝ} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) {c : EuclideanSpace ℝ (Fin d)} {R ρ : ℝ} (hρ : 0 < ρ)
    (hRρ : 5 * ρ ≤ R) (hu : MemLp u 2 (volume.restrict (Metric.ball c R)))
    (hcamp : CampanatoOn (Metric.ball c R) u α M) :
    campanatoLimit u =ᵐ[volume.restrict (Metric.ball c ρ)] u ∧
      HolderOnWith (Real.toNNReal (campanatoHolderConst d α * M)) (Real.toNNReal α)
        (campanatoLimit u) (Metric.ball c ρ) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hd)
  exact Haar.campanato_holderOnWith hα hM hρ hRρ hu hcamp

/-- **Converse of Campanato's characterisation.** A function that is Hölder of exponent `α`
with constant `K` on `Ω` satisfies the Campanato decay hypothesis on `Ω` with constant
`K · 2^α · √|B(0,1)|`. Squaring the mean-oscillation bound `K (2r)^α` and integrating over a ball
of volume `r^d |B(0,1)|` is the whole proof. -/
theorem campanatoOn_of_holderOnWith {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {α : ℝ} (hα : 0 < α) {K : ℝ≥0}
    (hu : HolderOnWith K (Real.toNNReal α) u Ω) :
    CampanatoOn Ω u α ((K : ℝ) * 2 ^ α * Real.sqrt (unitBallVolume d)) :=
  Haar.campanatoOn_of_holderOnWith hα hu

end EllipticPdes.Campanato
