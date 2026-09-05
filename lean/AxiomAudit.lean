/-
Axiom audit of the headline results.

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

/-! ### Dual space `H⁻¹` -/

/-- info: 'EllipticPdes.hneg_characterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.hneg_characterization

/-! ### Gårding inequality -/

/-- info: 'EllipticPdes.Sobolev.FullEllipticOp.garding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.FullEllipticOp.garding

/-! ### Fredholm alternative -/

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

/-! ### Resolvent bound and spectrum -/

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

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_two_mul_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.contDiffOn_holder_of_gradClosed

/-- info: 'EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_gradClosed_of_hasIteratedWeakDerivOn_le

/-- info: 'EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_contDiffOn_holder_ball_of_hasIteratedWeakDerivOn

/-- info: 'EllipticPdes.Regularity.exists_contDiffOn_holder_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_contDiffOn_holder_ball

/-! ### Base of the Poincaré chain -/

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

/-- info: 'EllipticPdes.Embedding.eLpNorm_le_of_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_le_of_mem_H01

/-- info: 'EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_of_isBounded

/-- info: 'EllipticPdes.Regularity.interior_holder_of_weakSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.interior_holder_of_weakSolution

/-- info: 'EllipticPdes.Embedding.eLpNorm_weakSolution_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_weakSolution_le

/-- info: 'EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact_of_le

/-- info: 'EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt

/-- info: 'EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_even

/-- info: 'EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_eLpNorm_le_of_gradClosed_fullStep

/-- info: 'EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_of_bound

/-- info: 'EllipticPdes.Embedding.not_isCompactOperator_critEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.not_isCompactOperator_critEmb

/-- info: 'EllipticPdes.Analysis.exists_weakLimit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.exists_weakLimit

/-- info: 'EllipticPdes.Embedding.exists_minimiser_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_minimiser_of_lt

/-- info: 'EllipticPdes.Sobolev.exists_principal_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_principal_eigenpair

/-- info: 'EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.principalEigenvalue_le_of_weak_eigen

/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair

/-- info: 'EllipticPdes.Sobolev.dirichlet_poincare_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_poincare_sharp

/-- info: 'EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.hasDerivAt_integral_abs_rpow

/-- info: 'EllipticPdes.Analysis.euler_lagrange_of_norm_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.euler_lagrange_of_norm_min

/-- info: 'EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt

/-- info: 'EllipticPdes.Sobolev.exists_higher_eigenpair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_higher_eigenpair

/-- info: 'EllipticPdes.Analysis.exists_bilin_minimiser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.exists_bilin_minimiser
/-- info: 'EllipticPdes.Analysis.euler_lagrange_of_bilin_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.euler_lagrange_of_bilin_min
/-- info: 'EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt
/-- info: 'EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_weakSolution_dirichlet_of_lt'
/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair_of_bounded
/-- info: 'EllipticPdes.Sobolev.exists_eigen_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_eigen_family

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigen_family_of_bounded

/-- info: 'EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_principal_eigenpair_ball

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigen_family_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigen_family_ball

/-- info: 'EllipticPdes.Sobolev.weak_eigenvalue_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.weak_eigenvalue_pos

/-- info: 'EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.solOp_finiteDimensional_eigenspace

/-- info: 'EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.dirichlet_eigenvalue_pos_ball

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_compactSupport

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_compactSupport_ideal

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_general

/-- info: 'EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.memLp_of_gradClosed_general_ideal

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_reflect

/-- info: 'EllipticPdes.Extension.partialD_comp_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.partialD_comp_reflect

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_translate

/-- info: 'EllipticPdes.Extension.partialD_comp_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.partialD_comp_shear

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_shear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_shear

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_chartExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_chartExt

/-- info: 'EllipticPdes.Extension.eLpNorm_chartExt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.eLpNorm_chartExt_le

/-- info: 'EllipticPdes.Extension.eLpNorm_chartExtGrad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.eLpNorm_chartExtGrad_le

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_comp_linearIsometry

/-- info: 'EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasWeakGradOn_mul_cutoff_inter

/-- info: 'EllipticPdes.Extension.exists_finite_chart_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_finite_chart_cover

/-- info: 'EllipticPdes.Extension.nonempty_boundaryPartition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.nonempty_boundaryPartition

/-- info: 'EllipticPdes.Extension.exists_localExtension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_localExtension

/-- info: 'EllipticPdes.Extension.exists_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extension

/-- info: 'EllipticPdes.Extension.exists_extension_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extension_subset

/-- info: 'EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Analysis.tendsto_eLpNorm_translate_sub

/-- info: 'EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.tendsto_eLpNorm_translate_convolution_sub

/-- info: 'EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_holderOnWith_of_gradClosed_general

/-- info: 'EllipticPdes.Embedding.morreyExponent_eq_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.morreyExponent_eq_ladder

/-! ### Norm bound of the extension operator -/

/-- info: 'EllipticPdes.Extension.exists_localExtension_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_localExtension_bound

/-- info: 'EllipticPdes.Extension.exists_extension_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extension_bound

/-- info: 'EllipticPdes.Extension.exists_extension_subset_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extension_subset_bound

/-! ### The extension operator as a linear map -/

/-- info: 'EllipticPdes.Extension.localExtension_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.localExtension_bound

/-- info: 'EllipticPdes.Extension.extension_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.extension_bound

/-- info: 'EllipticPdes.Extension.extension_subset_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.extension_subset_bound

/-- info: 'EllipticPdes.Extension.exists_extLinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extLinear

/-! ### Solvability and interior smoothness composed -/

/-- info: 'EllipticPdes.Regularity.exists_weakSolution_interior_smooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_weakSolution_interior_smooth

/-! ### Sobolev embedding on a bounded `C¹` domain -/

/-- info: 'EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_eLpNorm_sobolevConj_le_domain

/-- info: 'EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain

/-- info: 'EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_holderOnWith_of_gradClosed_domain

/-- info: 'EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_memLp_of_gradClosed_domain_ideal

/-- info: 'EllipticPdes.Embedding.exists_const_holderOnWith_domain_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_holderOnWith_domain_ideal

/-- info: 'EllipticPdes.Embedding.exists_const_holderOnWith_domain_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_holderOnWith_domain_free

/-! ### Classical derivatives up to the boundary -/

/-- info: 'EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_of_gradClosed_domain

/-- info: 'EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_ideal

/-- info: 'EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.exists_const_contDiffOn_holderOnWith_domain_free

/-! ### Global approximation and Rellich-Kondrachov on the graph space -/

/-- info: 'EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_smooth_tendsto_of_hasWeakGradOn

/-- info: 'EllipticPdes.Extension.exists_smooth_tendsto_of_mem_W12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_smooth_tendsto_of_mem_W12

/-- info: 'EllipticPdes.Sobolev.transL2_toLp_sub_le_of_hasWeakGradOn_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.transL2_toLp_sub_le_of_hasWeakGradOn_univ

/-- info: 'EllipticPdes.Regularity.norm_diffQuot_le_of_hasWeakDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.norm_diffQuot_le_of_hasWeakDeriv

/-- info: 'EllipticPdes.Regularity.weakDeriv_of_diffQuot_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.weakDeriv_of_diffQuot_bounded

/-- info: 'EllipticPdes.Embedding.morrey_ball_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.morrey_ball_contDiff

/-- info: 'EllipticPdes.Embedding.morrey_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.morrey_ball

/-- info: 'EllipticPdes.Sobolev.embW12_isCompact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.embW12_isCompact

/-! ### The Poincaré inequality with the mean subtracted -/

/-- info: 'EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.ae_const_of_hasWeakGradOn_zero

/-- info: 'EllipticPdes.Sobolev.poincare_wirtinger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.poincare_wirtinger

/-! ### The pointwise equation of a smooth representative -/

/-- info: 'EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.hasWeakGradOn_of_contDiffOn

/-- info: 'EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.weakSolution_ae_eq_of_contDiffOn

/-- info: 'EllipticPdes.Regularity.exists_weakSolution_interior_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Regularity.exists_weakSolution_interior_classical

/-! ### The unit ball as an instance of a bounded domain with `C¹` boundary -/

/-- info: 'EllipticPdes.Extension.hasC1Boundary_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.hasC1Boundary_ball

/-- info: 'EllipticPdes.Sobolev.embW12_isCompact_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.embW12_isCompact_ball

/-- info: 'EllipticPdes.Sobolev.poincare_wirtinger_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.poincare_wirtinger_ball

/-! ### The extension operator between the graph spaces -/

/-- info: 'EllipticPdes.Extension.mem_W12_of_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.mem_W12_of_hasWeakGradOn

/-- info: 'EllipticPdes.Extension.exists_extW12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Extension.exists_extW12

/-! ### Poincaré's inequality on a ball -/

/-- info: 'EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.hasWeakGradOn_comp_affineBall

/-- info: 'EllipticPdes.Sobolev.poincare_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.poincare_ball

/-! ### The chain rule and the weak maximum principle -/

/-- info: 'EllipticPdes.Embedding.hasWeakGradOn_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasWeakGradOn_comp

/-! ### Elementary properties of weak derivatives -/

/-- info: 'EllipticPdes.Embedding.hasWeakGradOn_unique_ae_of_locallyIntegrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasWeakGradOn_unique_ae_of_locallyIntegrableOn

/-- info: 'EllipticPdes.Embedding.HasWeakGradOn.add_of_locallyIntegrableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.HasWeakGradOn.add_of_locallyIntegrableOn

/-- info: 'EllipticPdes.Embedding.HasWeakGradOn.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.HasWeakGradOn.neg

/-- info: 'EllipticPdes.Embedding.HasWeakGradOn.const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.HasWeakGradOn.const_mul

/-- info: 'EllipticPdes.Embedding.HasWeakGradOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.HasWeakGradOn.mono

/-- info: 'EllipticPdes.Sobolev.instCompleteSpaceW12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.instCompleteSpaceW12

/-- info: 'EllipticPdes.Sobolev.instCompleteSpaceH01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.instCompleteSpaceH01

/-- info: 'EllipticPdes.Embedding.partialD_convolution_eq_of_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.partialD_convolution_eq_of_hasWeakGradOn

/-- info: 'EllipticPdes.Embedding.tendsto_eLpNorm_convolution_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.tendsto_eLpNorm_convolution_sub

/-- info: 'EllipticPdes.Embedding.hasWeakGradOn_posPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasWeakGradOn_posPart

/-- info: 'EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.ae_eq_zero_of_eq_const_of_hasWeakGradOn

/-- info: 'EllipticPdes.Sobolev.weak_maximum_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.weak_maximum_principle

/-! ### Truncation in `H₀¹` -/

/-- info: 'EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.mem_H01_of_hasCompactSupport

/-- info: 'EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_mem_H01_posPart_sub_const

/-- info: 'EllipticPdes.Sobolev.weak_maximum_principle_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.weak_maximum_principle_H01

/-- info: 'EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.eq_zero_of_weakSolution_H01

/-! ### The weak maximum principle with a transport term -/

/-- info: 'EllipticPdes.Sobolev.exists_truncation_mem_H01' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.exists_truncation_mem_H01

/-- info: 'EllipticPdes.Sobolev.weak_maximum_principle_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Sobolev.weak_maximum_principle_transport

/-- info: 'EllipticPdes.Embedding.hasWeakGradOn_negPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasWeakGradOn_negPart

/-- info: 'EllipticPdes.Embedding.hasWeakGradOn_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.hasWeakGradOn_abs

/-! ### The classical weak maximum principle -/

/-- info: 'EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef

/-- info: 'EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.sndFDeriv_nonpos_of_isLocalMax

/-- info: 'EllipticPdes.Classical.weak_maximum_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.weak_maximum_principle

/-- info: 'EllipticPdes.Classical.weak_minimum_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.weak_minimum_principle

/-- info: 'EllipticPdes.Classical.weak_maximum_principle_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.weak_maximum_principle_of_nonneg

/-- info: 'EllipticPdes.Classical.weak_minimum_principle_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.weak_minimum_principle_of_nonneg

/-! ### Hopf's lemma and the strong maximum principle -/

/-- info: 'EllipticPdes.Classical.hopf_lemma_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.hopf_lemma_ball

/-- info: 'EllipticPdes.Classical.hopf_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.hopf_lemma

/-- info: 'EllipticPdes.Classical.strong_maximum_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.strong_maximum_principle

/-- info: 'EllipticPdes.Classical.strong_maximum_principle_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.strong_maximum_principle_of_nonneg

/-! ### Corollaries of the strong maximum principle -/

/-- info: 'EllipticPdes.Classical.dirichlet_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.dirichlet_unique

/-- info: 'EllipticPdes.Classical.hopf_lemma_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.hopf_lemma_of_zero

/-- info: 'EllipticPdes.Classical.strong_maximum_principle_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.strong_maximum_principle_of_zero

/-- info: 'EllipticPdes.Classical.avoidance_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.avoidance_principle

/-- info: 'EllipticPdes.Classical.eq_of_eq_of_fderiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.eq_of_eq_of_fderiv_eq

/-- info: 'EllipticPdes.Classical.neumann_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.neumann_unique

/-- info: 'EllipticPdes.Classical.neumann_unique_of_exists_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.neumann_unique_of_exists_pos

/-! ### A priori bound from the maximum principle -/

/-- info: 'EllipticPdes.Classical.apriori_bound_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.apriori_bound_sub

/-- info: 'EllipticPdes.Classical.apriori_bound_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.apriori_bound_abs

/-! ### Subharmonic and harmonic functions -/

/-- info: 'EllipticPdes.Classical.weak_maximum_principle_subharmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.weak_maximum_principle_subharmonic

/-- info: 'EllipticPdes.Classical.strong_maximum_principle_subharmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.strong_maximum_principle_subharmonic

/-- info: 'EllipticPdes.Classical.strong_minimum_principle_superharmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.strong_minimum_principle_superharmonic

/-- info: 'EllipticPdes.Classical.harmonic_const_of_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.harmonic_const_of_max

/-- info: 'EllipticPdes.Classical.harmonic_const_of_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.harmonic_const_of_min

/-- info: 'EllipticPdes.Classical.dirichlet_unique_harmonic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.dirichlet_unique_harmonic

/-- info: 'EllipticPdes.Classical.not_isLocalMax_of_nondivOp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.not_isLocalMax_of_nondivOp_neg

/-- info: 'EllipticPdes.Classical.comparison_principle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.comparison_principle

/-- info: 'EllipticPdes.Classical.abs_le_of_nondivOp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Classical.abs_le_of_nondivOp_eq_zero

/-- info: 'EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms EllipticPdes.Embedding.eLpNorm_le_of_mem_H01_two
