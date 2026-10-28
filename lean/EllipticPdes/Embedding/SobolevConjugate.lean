/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Sobolev conjugate

Evans §5.6.1 (p. 277) defines, for `1 ≤ p < n`, the Sobolev conjugate `p* := n p / (n - p)` and
notes that `1/p* = 1/p - 1/n` and `p* > p`. The first identity is the hypothesis shape of
`Embedding.exists_eLpNorm_sobolevConj_le_compactSupport`.

## Main declarations

* `EllipticPdes.Embedding.sobolevConj`: the Sobolev conjugate `n p / (n - p)`.
* `EllipticPdes.Embedding.inv_sobolevConj`: `1/p* = 1/p - 1/n`.
* `EllipticPdes.Embedding.lt_sobolevConj`: `p < p*`.

## References

L. C. Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 (p. 277).
-/

@[expose] public section

open scoped NNReal

namespace EllipticPdes.Embedding

/-- **Sobolev conjugate** `n p / (n - p)` of the exponent `p` in dimension `n` (Evans §5.6.1,
p. 277). The truncated subtraction agrees with the real one because the lemmas assume `p < n`. -/
noncomputable def sobolevConj (n p : ℝ≥0) : ℝ≥0 := n * p / (n - p)

variable {n p : ℝ≥0}

/-- **Reciprocal of the Sobolev conjugate.** For `1 ≤ p < n`, `1/p* = 1/p - 1/n`. -/
theorem inv_sobolevConj (hp : 1 ≤ p) (hpn : p < n) :
    ((sobolevConj n p : ℝ≥0) : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le one_pos hp
  have hn0 : (0 : ℝ) < n := hp0.trans (by exact_mod_cast hpn)
  have hnp : (0 : ℝ) < (n : ℝ) - p := sub_pos.2 (by exact_mod_cast hpn)
  rw [sobolevConj, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_sub hpn.le]
  field_simp

/-- **Sobolev conjugate above the exponent.** For `1 ≤ p < n`, `p < p*`. -/
theorem lt_sobolevConj (hp : 1 ≤ p) (hpn : p < n) : p < sobolevConj n p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast lt_of_lt_of_le one_pos hp
  have hn0 : (0 : ℝ) < n := hp0.trans (by exact_mod_cast hpn)
  have hnp : (0 : ℝ) < (n : ℝ) - p := sub_pos.2 (by exact_mod_cast hpn)
  rw [← NNReal.coe_lt_coe, sobolevConj, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_sub hpn.le, lt_div_iff₀ hnp]
  have : (p : ℝ) < n := by exact_mod_cast hpn
  nlinarith

end EllipticPdes.Embedding
