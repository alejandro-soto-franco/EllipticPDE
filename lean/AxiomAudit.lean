/-
Axiom gates for the headline results.

Each declaration the README claims is pinned here to the three axioms of
classical Lean: `propext`, `Classical.choice` and `Quot.sound`. `#guard_msgs`
turns a change in the axiom set into a build error, so a `sorryAx` reaching any
of these, or a new axiom entering through a dependency, fails `lake build`
rather than passing unnoticed.

`whitespace := lax` is required because the pretty printer wraps the longer
declaration names across lines.

This module is a build target in its own right. It is not imported by
`EllipticPdes`, and nothing imports it.
-/
import EllipticPdes

/-! ### Existence and uniqueness -/

/-- info: 'EllipticPdes.dirichlet_weak_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.dirichlet_weak_solution

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.existence_three_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.existence_three_of_bounded

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.weak_solution_L2_of_nonneg_zeroth_of_bounded

/-! ### The dual space `H⁻¹` -/

/-- info: 'EllipticPdes.hneg_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.hneg_characterization

/-! ### The Gårding inequality -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.garding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.garding

/-! ### The Fredholm alternative -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.finiteDimensional_solSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.finiteDimensional_solSpace

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.finrank_solSpaceStar_eq_finrank_solSpace

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.solvable_iff_orthogonal_solSpaceStar

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.fredholm_alternative_of_bounded

/-! ### The resolvent bound and the spectrum -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.resolvent_bound_of_bounded

/-- info: 'EllipticPdes.Sobolev.spectrum_compact_operator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.spectrum_compact_operator

/-- info: 'EllipticPdes.Sobolev.solOp_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.solOp_spectral

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral

/-- info: 'EllipticPdes.Sobolev.dirichlet_spectral_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_spectral_of_bounded

/-- info: 'EllipticPdes.Sobolev.symmetric_fullElliptic_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.symmetric_fullElliptic_spectral

/-! ### Interior regularity -/

/-- info: 'EllipticPdes.Regularity.interior_H2_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_H2_estimate

/-- info: 'EllipticPdes.Regularity.interior_cutoffGrad_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_cutoffGrad_mem_H01

/-- info: 'EllipticPdes.Regularity.caccioppoli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.caccioppoli

/-! ### Higher interior regularity -/

/-- info: 'EllipticPdes.Regularity.HasWeakDeriv.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.HasWeakDeriv.unique

/-- info: 'EllipticPdes.Regularity.setIntegral_mul_partialD_cut_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.setIntegral_mul_partialD_cut_eq

/-- info: 'EllipticPdes.Regularity.outer_secondWeakDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.outer_secondWeakDeriv

/-- info: 'EllipticPdes.Regularity.localWeakForm_of_fullBilin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.localWeakForm_of_fullBilin

/-- info: 'EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.differentiated_weakForm_of_weakSolution

/-- info: 'EllipticPdes.Regularity.higher_interior_regularity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.higher_interior_regularity

/-- info: 'EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn

/-! ### Campanato's characterisation of Hölder continuity -/

/-- info: 'EllipticPdes.Campanato.campanato_holderOnWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Campanato.campanato_holderOnWith

/-- info: 'EllipticPdes.Campanato.campanatoOn_of_holderOnWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Campanato.campanatoOn_of_holderOnWith

/-! ### Boundary regularity -/

/-- info: 'EllipticPdes.Regularity.cutoffMulOn_tangDiffQuotG_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.cutoffMulOn_tangDiffQuotG_mem_H01

/-- info: 'EllipticPdes.Regularity.HasWeakDerivOn.of_mul_contDiff_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.HasWeakDerivOn.of_mul_contDiff_left

/-- info: 'EllipticPdes.Regularity.exists_hasWeakDerivOn_of_mul_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_hasWeakDerivOn_of_mul_diag

/-! ### Classical regularity -/

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate_two

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_of_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_six_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_six_le

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_four_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_four_le

/-- info: 'EllipticPdes.Embedding.interior_holder_estimate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.interior_holder_estimate_one

/-- info: 'EllipticPdes.Embedding.memLp_two_mul_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_two_mul_of_gradClosed

/-- info: 'EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasFDerivAt_of_continuousOn_hasWeakGradOn

/-- info: 'EllipticPdes.Embedding.contDiffOn_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.contDiffOn_of_gradClosed

/-- info: 'EllipticPdes.Regularity.interior_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_smooth

/-! ### The Poincaré chain the library reduces to -/

/-- info: 'EllipticPdes.Poincare.intervalIntegral_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.intervalIntegral_mul_sq_le

/-- info: 'EllipticPdes.Poincare.poincare_oneDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_oneDim

/-- info: 'EllipticPdes.Poincare.poincare_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_domain

/-- info: 'EllipticPdes.Poincare.poincare_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01

/-- info: 'EllipticPdes.Poincare.poincare_H01_euclBox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01_euclBox

/-- info: 'EllipticPdes.Poincare.poincare_H01_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Poincare.poincare_H01_of_bounded
