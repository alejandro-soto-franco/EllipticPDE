/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ball means and the Campanato decay hypothesis

The `C^{k,α}` scale of Schauder theory rests on Campanato's characterisation of Hölder
continuity: a function whose mean oscillation over balls decays like `r^α` has a Hölder
representative of exponent `α`. This file fixes the two objects that characterisation is
stated through, over a finite-dimensional real normed space `E` whose volume measure is an
additive Haar measure: the mean

  `u_{x,r} = ⨍_{B(x,r)} u`

written `ballAverage u x r`, and the decay hypothesis

  `∫_{B(x,r)} |u - u_{x,r}|² ≤ M² r^{d + 2α}` for every ball `B(x,r) ⊆ Ω`, with `d = dim E`,

written `CampanatoOn Ω u α M`. The hypothesis quantifies over balls contained in `Ω`, which is
the form property (H3) of Fernández-Real and Ros-Oton takes, so every mean in sight is a mean
over a ball and has the exact volume `r^d · |B(0,1)|`.

The rest of the file records what the estimates downstream need: the volume of a ball as a real
number, and the integrability of `u` and of `(u - c)²` on a ball, both read off from
`MemLp u 2 (volume.restrict Ω)`. The Euclidean statements, with `d` the number of coordinates,
are the specialisations at the end of `EllipticPdes.Campanato.Converse`.
-/

@[expose] public section

open MeasureTheory Set Metric Module

open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Campanato.Haar

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]

/-- The volume of the unit ball of `E`, as a real number. Every ball volume is a multiple of
it, so it is convenient to name it once. -/
def unitBallVolume : ℝ := volume.real (Metric.ball (0 : E) 1)

variable {E}

/-- The dimension of `E`, the exponent of the volume of a ball. -/
local notation "𝔡" => Module.finrank ℝ E

omit [BorelSpace E] in
/-- The unit ball has positive volume. -/
theorem unitBallVolume_pos : 0 < unitBallVolume E := by
  rw [unitBallVolume, measureReal_def]
  exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- The volume of `B(x, r)` is `r^d` times the volume of the unit ball. -/
theorem measureReal_ball (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ 𝔡 * unitBallVolume E := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), unitBallVolume, measureReal_def]

/-- The volume of `B(x, r)` written with a real exponent, the form the decay hypothesis uses. -/
theorem measureReal_ball_rpow (x : E) {r : ℝ} (hr : 0 < r) :
    volume.real (Metric.ball x r) = r ^ (𝔡 : ℝ) * unitBallVolume E := by
  rw [measureReal_ball x hr, Real.rpow_natCast]

/-- The restriction of Haar measure to a ball is finite. -/
instance isFiniteMeasure_restrict_ball (x : E) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball x r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- **Mean of `u` over the ball `B(x, r)`.** Campanato's hypothesis measures the oscillation
of `u` about this value, and the characterisation produces the Hölder representative as the limit
of these means as `r → 0`. -/
def ballAverage (u : E → ℝ) (x : E) (r : ℝ) : ℝ :=
  ⨍ y in Metric.ball x r, u y

/-- **Campanato decay hypothesis.** The mean oscillation of `u` over every ball contained in
`Ω` decays at the rate `r^{d + 2α}`, with constant `M`. For `0 < α ≤ 1` this forces `u` to have a
Hölder representative of exponent `α` on the interior of `Ω`; that is the content of
`EllipticPdes.Campanato.Haar.campanato_holderOnWith`. -/
def CampanatoOn (Ω : Set E) (u : E → ℝ) (α M : ℝ) : Prop :=
  ∀ (x : E) (r : ℝ), 0 < r → Metric.ball x r ⊆ Ω →
    ∫ y in Metric.ball x r, (u y - ballAverage u x r) ^ 2 ≤ M ^ 2 * r ^ ((𝔡 : ℝ) + 2 * α)

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The decay hypothesis weakens when the constant grows. -/
theorem CampanatoOn.mono {Ω : Set E} {u : E → ℝ} {α M M' : ℝ} (h : CampanatoOn Ω u α M)
    (hM : 0 ≤ M) (hMM : M ≤ M') : CampanatoOn Ω u α M' := by
  intro x r hr hsub
  refine (h x r hr hsub).trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hr.le _))
  exact pow_le_pow_left₀ hM hMM 2

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The decay hypothesis shrinks with the domain. -/
theorem CampanatoOn.mono_set {Ω Ω' : Set E} {u : E → ℝ} {α M : ℝ} (h : CampanatoOn Ω u α M)
    (hΩ : Ω' ⊆ Ω) : CampanatoOn Ω' u α M :=
  fun x r hr hsub => h x r hr (hsub.trans hΩ)

section Integrability

variable {Ω : Set E} {u : E → ℝ}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] in
/-- Square integrability on `Ω` restricts to any ball inside `Ω`. -/
theorem memLp_two_ball (hu : MemLp u 2 (volume.restrict Ω)) {x : E} {r : ℝ}
    (hsub : Metric.ball x r ⊆ Ω) : MemLp u 2 (volume.restrict (Metric.ball x r)) :=
  hu.mono_measure (Measure.restrict_mono hsub le_rfl)

omit [BorelSpace E] in
/-- Subtracting a constant preserves square integrability on a ball. -/
theorem memLp_two_sub_const (hu : MemLp u 2 (volume.restrict Ω)) {x : E} {r : ℝ}
    (hsub : Metric.ball x r ⊆ Ω) (c : ℝ) :
    MemLp (fun y => u y - c) 2 (volume.restrict (Metric.ball x r)) :=
  (memLp_two_ball hu hsub).sub (memLp_const c)

omit [BorelSpace E] in
/-- The squared deviation of `u` from a constant is integrable on a ball inside `Ω`. -/
theorem integrableOn_sq_sub_const (hu : MemLp u 2 (volume.restrict Ω)) {x : E} {r : ℝ}
    (hsub : Metric.ball x r ⊆ Ω) (c : ℝ) :
    IntegrableOn (fun y => (u y - c) ^ 2) (Metric.ball x r) volume :=
  (memLp_two_sub_const hu hsub c).integrable_sq

end Integrability

end EllipticPdes.Campanato.Haar
