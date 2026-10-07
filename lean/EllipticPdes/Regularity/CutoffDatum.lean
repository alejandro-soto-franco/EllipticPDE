/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Regularity.DatumPiece
public import EllipticPdes.Regularity.LocalWeakFormWkInfty

/-!
# Datum of the induction step

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 step 3 produces an equation
for the cut-off derivative whose datum is a fixed list of shapes. Each is the middle cutoff of
the tower, or one of its first two partial derivatives, against a coefficient of the operator or
one of its derivatives, against a derivative of the solution of order at most two.

This file builds that datum as a single `L²(Ω)` class, with its order-`k` family, its bound and
its pairing. Nothing here knows how the list arose: the expansion of the bilinear form and the
differentiated equation both live in `EllipticPdes.Regularity.HigherInterior`, and what they
need of the datum is exactly the three conclusions below.

The constant is quantified before the solution, the datum and the direction of differentiation.
The shapes that differentiate a coefficient in the direction the equation is differentiated
depend on that direction, so their constants are collected over it.

## Main declarations

* `exists_cutoffDatum`: the datum, its family, its bound and its pairing.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {n : ℕ}

/-- **Shapes of the datum that carry the cutoff itself.** Seven of the twelve shapes of Evans,
*Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 2 step 3: the cutoff `ξ` against a
coefficient of the operator or one of its derivatives, against a derivative of the solution `uN`
of order at most two on the collar `N`, integrated against the test function `v`. `Df` is the
derivative of the datum in the direction `ℓ`. -/
def cutoffDatumPairingCutoff (Op : FullEllipticOp (n + 1))
    {N : Set (EuclideanSpace ℝ (Fin (n + 1)))} {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    (ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ℓ : Fin (n + 1)) {uN : L2D N} (Df : L2D N)
    (HuN : HasIteratedWeakDerivOn N (k + 2) uN) (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : ℝ :=
  (∫ x in N, ξ x * ((1 : ℝ) * (Df x : ℝ)) * v x)
    - (∑ i, ∫ x in N, ξ x * ((hbc.bReg i).D [ℓ] x * (HuN.D [i] x : ℝ)) * v x)
    - (∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [ℓ, i] x : ℝ)) * v x)
    - (∫ x in N, ξ x * (hbc.cReg.D [ℓ] x * (uN x : ℝ)) * v x)
    + (∑ i, ∑ j, ∫ x in N, ξ x * (hA.D [j, ℓ] i j x * (HuN.D [i] x : ℝ)) * v x)
    + (∑ i, ∑ j, ∫ x in N, ξ x * (hA.D [ℓ] i j x * (HuN.D [j, i] x : ℝ)) * v x)
    + ∑ i, ∫ x in N, ξ x * (Op.b x i * (HuN.D [i, ℓ] x : ℝ)) * v x

/-- **Shapes of the datum that carry a derivative of the cutoff.** The other five shapes: the
first or second partial derivatives of `ξ` against a coefficient of the operator or its
derivative, against a derivative of the solution `uN` of order at most two. -/
def cutoffDatumPairingGrad (Op : FullEllipticOp (n + 1))
    {N : Set (EuclideanSpace ℝ (Fin (n + 1)))} {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2))
    (ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ℓ : Fin (n + 1)) {uN : L2D N}
    (HuN : HasIteratedWeakDerivOn N (k + 2) uN) (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : ℝ :=
  (∑ i, ∫ x in N, partialD i ξ x * (Op.b x i * (HuN.D [ℓ] x : ℝ)) * v x)
    - (∑ i, ∑ j, ∫ x in N, partialD j ξ x * (Op.a x i j * (HuN.D [i, ℓ] x : ℝ)) * v x)
    - (∑ i, ∑ j, ∫ x in N,
        partialD j (partialD i ξ) x * (Op.a x i j * (HuN.D [ℓ] x : ℝ)) * v x)
    - (∑ i, ∑ j, ∫ x in N, partialD i ξ x * (hA.D [j] i j x * (HuN.D [ℓ] x : ℝ)) * v x)
    - (∑ i, ∑ j, ∫ x in N, partialD i ξ x * (Op.a x i j * (HuN.D [j, ℓ] x : ℝ)) * v x)

/-- **Pairing of the datum of the induction step with a test function.** The twelve shapes of
`cutoffDatumPairingCutoff` and `cutoffDatumPairingGrad`. -/
def cutoffDatumPairing (Op : FullEllipticOp (n + 1))
    {N : Set (EuclideanSpace ℝ (Fin (n + 1)))} {k : ℕ}
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    (ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (ℓ : Fin (n + 1)) {uN : L2D N} (Df : L2D N)
    (HuN : HasIteratedWeakDerivOn N (k + 2) uN) (v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : ℝ :=
  cutoffDatumPairingCutoff Op hA hbc ξ ℓ Df HuN v + cutoffDatumPairingGrad Op hA ξ ℓ HuN v

/-- **A constant for a family of datum pairings.** For the pairings `T ℓ Df HuN` there is a
constant such that every family of derivatives `HuN` of the solution on the collar `N` and every
derivative `Df` of the datum, bounded by `B`, yield an `L²(Ω)` class with `k` weak derivatives
bounded by `K·B` that pairs as `T`. The constant is quantified before the direction `ℓ`, the
solution and the datum. -/
def HasCutoffDatum (Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))) (k : ℕ)
    (T : Fin (n + 1) → ∀ {uN : L2D N}, L2D N → HasIteratedWeakDerivOn N (k + 2) uN →
      (EuclideanSpace ℝ (Fin (n + 1)) → ℝ) → ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (ℓ : Fin (n + 1)) (uN Df : L2D N)
    (HuN : HasIteratedWeakDerivOn N (k + 2) uN) (HDf : HasIteratedWeakDerivOn N k Df) (B : ℝ),
    IteratedL2Bound HuN B → IteratedL2Bound HDf B → IsDatumPairing Ω k (K * B) (T ℓ Df HuN)

namespace HasCutoffDatum

variable {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))} {k : ℕ}

/-- Datum pairings add, with the constants. -/
theorem add {T T' : Fin (n + 1) → ∀ {uN : L2D N}, L2D N →
      HasIteratedWeakDerivOn N (k + 2) uN → (EuclideanSpace ℝ (Fin (n + 1)) → ℝ) → ℝ}
    (h : HasCutoffDatum Ω N k T) (h' : HasCutoffDatum Ω N k T') :
    HasCutoffDatum Ω N k fun ℓ _ Df HuN v => T ℓ Df HuN v + T' ℓ Df HuN v := by
  obtain ⟨K, hK, hT⟩ := h
  obtain ⟨K', hK', hT'⟩ := h'
  refine ⟨K + K', add_nonneg hK hK', fun ℓ uN Df HuN HDf B hHuN hHDf => ?_⟩
  exact ((hT ℓ uN Df HuN HDf B hHuN hHDf).add (hT' ℓ uN Df HuN HDf B hHuN hHDf)).mono
    (le_of_eq (add_mul K K' B).symm)

end HasCutoffDatum

variable {Ω N : Set (EuclideanSpace ℝ (Fin (n + 1)))} {k : ℕ}

/-- The shapes carrying the cutoff have a datum with a constant independent of the solution. -/
theorem hasCutoffDatum_cutoff (Op : FullEllipticOp (n + 1))
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) :
    HasCutoffDatum Ω N k fun ℓ _ Df HuN => cutoffDatumPairingCutoff Op hA hbc ξ ℓ Df HuN := by
  classical
  have hb : ∀ i : Fin (n + 1), IsWkInfty (fun x => Op.b x i) k :=
    fun i => (hbc.bReg i).mono (by omega)
  obtain ⟨K1, hK1, hP1⟩ := exists_datum_of_pieces (ι := Unit) (χ := fun _ => ξ)
    (a := fun _ _ => (1 : ℝ)) hNm hNΩ k (fun _ => hξ) fun _ => IsWkInfty.const 1 k
  obtain ⟨K2, hK2, hP2⟩ := exists_datum_of_pieces_dir (σ := Fin (n + 1))
    (χ := fun _ : Fin (n + 1) => ξ) (a := fun m i => (hbc.bReg i).D [m]) hNm hNΩ k
    (fun _ => hξ) fun m i => ((hbc.bReg i).deriv m).mono (by omega)
  obtain ⟨K3, hK3, hP3⟩ := exists_datum_of_pieces (χ := fun _ : Fin (n + 1) => ξ) hNm hNΩ k
    (fun _ => hξ) hb
  obtain ⟨K4, hK4, hP4⟩ := exists_datum_of_pieces_dir (σ := Fin (n + 1))
    (χ := fun _ : Unit => ξ) (a := fun m _ => hbc.cReg.D [m]) hNm hNΩ k (fun _ => hξ)
    fun m _ => (hbc.cReg.deriv m).mono (by omega)
  obtain ⟨K5, hK5, hP5⟩ := exists_datum_of_pieces_dir (σ := Fin (n + 1))
    (χ := fun _ : Fin (n + 1) × Fin (n + 1) => ξ) (a := fun m t => hA.D [t.2, m] t.1 t.2)
    hNm hNΩ k (fun _ => hξ) fun m t => (((hA.entry t.1 t.2).deriv m).deriv t.2).mono (by omega)
  obtain ⟨K6, hK6, hP6⟩ := exists_datum_of_pieces_dir (σ := Fin (n + 1))
    (χ := fun _ : Fin (n + 1) × Fin (n + 1) => ξ) (a := fun m t => hA.D [m] t.1 t.2)
    hNm hNΩ k (fun _ => hξ) fun m t => ((hA.entry t.1 t.2).deriv m).mono (by omega)
  refine ⟨K1 + K2 + 2 * K3 + K4 + K5 + K6, by positivity, ?_⟩
  intro ℓ uN Df HuN HDf B hHuN hHDf
  have hB0 : 0 ≤ B := (norm_nonneg uN).trans hHuN.norm_le
  have h := (((((hP1 (fun _ => Df) (fun _ => HDf) fun _ => hHDf).sub
    (hP2 ℓ (fun i => HuN.D [i]) (fun i => HuN.deriv₁ i) hB0 fun i => hHuN.deriv₁ i)).sub
    (hP3 (fun i => HuN.D [ℓ, i]) (fun i => HuN.deriv₂ i ℓ) fun i => hHuN.deriv₂ i ℓ)).sub
    (hP4 ℓ (fun _ => uN) (fun _ => HuN.mono (Nat.le_add_right k 2)) hB0
      fun _ => hHuN.mono_order (Nat.le_add_right k 2))).add
    (hP5 ℓ (fun t => HuN.D [t.1]) (fun t => HuN.deriv₁ t.1) hB0 fun t => hHuN.deriv₁ t.1)).add
    (hP6 ℓ (fun t => HuN.D [t.2, t.1]) (fun t => HuN.deriv₂ t.1 t.2) hB0
      fun t => hHuN.deriv₂ t.1 t.2)
  refine (h.add (hP3 (fun i => HuN.D [i, ℓ]) (fun i => HuN.deriv₂ ℓ i)
    fun i => hHuN.deriv₂ ℓ i)).mono (le_of_eq (by ring)) |>.congr fun v _ _ => ?_
  simp [cutoffDatumPairingCutoff, Fintype.sum_prod_type]

/-- The shapes carrying a derivative of the cutoff have a datum with a constant independent of
the solution. -/
theorem hasCutoffDatum_grad (Op : FullEllipticOp (n + 1))
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) :
    HasCutoffDatum Ω N k fun ℓ _ _ HuN => cutoffDatumPairingGrad Op hA ξ ℓ HuN := by
  classical
  have hξD : ∀ i : Fin (n + 1), IsTestFn N (partialD i ξ) := fun i => isTestFn_partialD hξ i
  have hb : ∀ i : Fin (n + 1), IsWkInfty (fun x => Op.b x i) k :=
    fun i => (hbc.bReg i).mono (by omega)
  have ha : ∀ t : Fin (n + 1) × Fin (n + 1), IsWkInfty (fun x => Op.a x t.1 t.2) k :=
    fun t => (hA.entry t.1 t.2).mono (by omega)
  obtain ⟨K7, hK7, hP7⟩ := exists_datum_of_pieces hNm hNΩ k
    (fun t : Fin (n + 1) × Fin (n + 1) => hξD t.2) ha
  obtain ⟨K8, hK8, hP8⟩ := exists_datum_of_pieces hNm hNΩ k
    (fun t : Fin (n + 1) × Fin (n + 1) => isTestFn_partialD (hξD t.1) t.2) ha
  obtain ⟨K9, hK9, hP9⟩ := exists_datum_of_pieces hNm hNΩ k
    (a := fun t : Fin (n + 1) × Fin (n + 1) => hA.D [t.2] t.1 t.2) (fun t => hξD t.1)
    fun t => ((hA.entry t.1 t.2).deriv t.2).mono (by omega)
  obtain ⟨K10, hK10, hP10⟩ := exists_datum_of_pieces hNm hNΩ k
    (fun t : Fin (n + 1) × Fin (n + 1) => hξD t.1) ha
  obtain ⟨K11, hK11, hP11⟩ := exists_datum_of_pieces hNm hNΩ k hξD hb
  refine ⟨K11 + K7 + K8 + K9 + K10, by positivity, ?_⟩
  intro ℓ uN Df HuN HDf B hHuN hHDf
  have h := ((((hP11 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ) fun _ => hHuN.deriv₁ ℓ).sub
    (hP7 (fun t => HuN.D [t.1, ℓ]) (fun t => HuN.deriv₂ ℓ t.1) fun t => hHuN.deriv₂ ℓ t.1)).sub
    (hP8 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ) fun _ => hHuN.deriv₁ ℓ)).sub
    (hP9 (fun _ => HuN.D [ℓ]) (fun _ => HuN.deriv₁ ℓ) fun _ => hHuN.deriv₁ ℓ)).sub
    (hP10 (fun t => HuN.D [t.2, ℓ]) (fun t => HuN.deriv₂ ℓ t.2) fun t => hHuN.deriv₂ ℓ t.2)
  refine (h.mono (le_of_eq (by ring))).congr fun v _ _ => ?_
  simp [cutoffDatumPairingGrad, Fintype.sum_prod_type]

/-- **Datum of the induction step.** For a cutoff `ξ` supported in the collar `N ⊆ Ω`, there
is a constant such that every family of derivatives of the solution on `N` bounded by `B`, and
every derivative of the datum bounded by `B`, produce an `L²(Ω)` class with `k` weak derivatives
bounded by `K·B` and pairing against a test function as the twelve shapes.

The two shapes with the zeroth-order coefficient against the differentiated solution cancel
between the differentiated equation and the zeroth-order block, and are absent. The two with the
transport coefficient do not, because the equation names one order of differentiation and the
block the other, and only the symmetry of the mixed second derivatives identifies them. -/
theorem exists_cutoffDatum (Op : FullEllipticOp (n + 1))
    (hNm : MeasurableSet N) (hNΩ : N ⊆ Ω)
    (hA : IsWkInftyCoeff Op.toEllipticCoeff (k + 2)) (hbc : IsWkInftyLower Op (k + 1))
    {ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hξ : IsTestFn N ξ) :
    HasCutoffDatum Ω N k fun ℓ _ Df HuN => cutoffDatumPairing Op hA hbc ξ ℓ Df HuN :=
  (hasCutoffDatum_cutoff Op hNm hNΩ hA hbc hξ).add (hasCutoffDatum_grad Op hNm hNΩ hA hbc hξ)

end EllipticPdes.Regularity
