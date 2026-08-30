/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticPdes.Sobolev.Basic
import EllipticPdes.Sobolev.Coefficients
import EllipticPdes.Regularity.DifferenceQuotient
import EllipticPdes.Regularity.DiffQuotientBound
import EllipticPdes.Poincare.OneDim
import EllipticPdes.Poincare.Fubini
import EllipticPdes.Poincare.Domain
import EllipticPdes.Poincare.Density
import EllipticPdes.Poincare.Geometry
import EllipticPdes.Poincare.BoxSlice
import EllipticPdes.Poincare.BoundedDomain
import EllipticPdes.Form.BilinearForm
import EllipticPdes.Form.Hneg
import EllipticPdes.Existence.Existence
import EllipticPdes.Form.GeneralForm
import EllipticPdes.Existence.Garding
import EllipticPdes.Regularity.Caccioppoli
import EllipticPdes.Regularity.InteriorCompactSupport
import EllipticPdes.Regularity.CoeffC1
import EllipticPdes.Regularity.CoeffC2
import EllipticPdes.Regularity.CoeffCk
import EllipticPdes.Regularity.CoeffWkInfty
import EllipticPdes.Regularity.CoeffBridge
import EllipticPdes.Regularity.MollifyWkInfty
import EllipticPdes.Regularity.LowerOrderWkInfty
import EllipticPdes.Regularity.CutoffTower
import EllipticPdes.Regularity.RestrictedDiffQuotient
import EllipticPdes.Regularity.RestrictedDiffQuotientMem
import EllipticPdes.Regularity.Interior.Support
import EllipticPdes.Regularity.Interior.EnergyBound
import EllipticPdes.Regularity.Interior.NormBound
import EllipticPdes.Regularity.Interior
import EllipticPdes.Regularity.LeibnizWkInfty
import EllipticPdes.Regularity.DifferentiatedWkInfty
import EllipticPdes.Regularity.LocalWeakFormWkInfty
import EllipticPdes.Regularity.WeakFormDense
import EllipticPdes.Regularity.HigherWeakDeriv
import EllipticPdes.Regularity.MulIterated
import EllipticPdes.Regularity.IteratedSum
import EllipticPdes.Regularity.IteratedRestrict
import EllipticPdes.Regularity.L2Pairing
import EllipticPdes.Regularity.ExtendCutoff
import EllipticPdes.Regularity.WeakDerivOnSymm
import EllipticPdes.Regularity.CutoffGradFormula
import EllipticPdes.Regularity.CollarIdentify
import EllipticPdes.Regularity.CutoffCommutator
import EllipticPdes.Regularity.DatumPiece
import EllipticPdes.Regularity.CutoffDatum
import EllipticPdes.Regularity.SmoothGlue
import EllipticPdes.Regularity.HigherInterior
import EllipticPdes.Regularity.IteratedFamily
import EllipticPdes.Regularity.InteriorSmooth
import EllipticPdes.Regularity.InteriorHolderFinite
import EllipticPdes.Regularity.DifferentiatedEquation
import EllipticPdes.Regularity.Boundary.HalfBall
import EllipticPdes.Regularity.Boundary.TangentialDiffQuotient
import EllipticPdes.Regularity.Boundary.TangentialDiffQuotientMem
import EllipticPdes.Regularity.Boundary.WeakQuotientRule
import EllipticPdes.Regularity.WeakLimit
import EllipticPdes.Regularity.CutoffDeriv
import EllipticPdes.Regularity.WeakDerivUnique
import EllipticPdes.Regularity.TestFnCut
import EllipticPdes.Regularity.OuterCutoffTower
import EllipticPdes.Regularity.LocalWeakForm
import EllipticPdes.Embedding.WeakGradient
import EllipticPdes.Embedding.Convolution
import EllipticPdes.Embedding.MorreyOneDim
import EllipticPdes.Embedding.RayIntegral
import EllipticPdes.Embedding.Morrey
import EllipticPdes.Embedding.WeakDerivBridge
import EllipticPdes.Campanato.Basic
import EllipticPdes.Campanato.Compare
import EllipticPdes.Campanato.Telescope
import EllipticPdes.Campanato.Holder
import EllipticPdes.Campanato.Converse
import EllipticPdes.Embedding.GagliardoNirenberg
import EllipticPdes.Embedding.SobolevLadder
import EllipticPdes.Embedding.SobolevLadderFullStep
import EllipticPdes.Embedding.WeakGradUnique
import EllipticPdes.Embedding.ClassicalDeriv
import EllipticPdes.Embedding.SmoothOfGradClosed
import EllipticPdes.Embedding.HolderOfGradClosed
import EllipticPdes.Embedding.InteriorHolder
import EllipticPdes.Fredholm.Fredholm
import EllipticPdes.Fredholm.FredholmComplete
import EllipticPdes.Spectrum.SpectrumSigma
import EllipticPdes.Fredholm.Compactness
import EllipticPdes.Spectrum.Spectrum
import EllipticPdes.Spectrum.RellichDischarge
import EllipticPdes.BoundedInstances
import EllipticPdes.Analysis.WeakCompactness
import EllipticPdes.Analysis.LpInterpolation
import EllipticPdes.Analysis.Dilation
import EllipticPdes.Embedding.H01Sobolev
import EllipticPdes.Embedding.SobolevSolution
import EllipticPdes.Embedding.RellichLq
import EllipticPdes.Embedding.SobolevSharp
import EllipticPdes.Analysis.LqDerivative
import EllipticPdes.Analysis.LqEulerLagrange
import EllipticPdes.Embedding.DirectMethod
import EllipticPdes.Regularity.InteriorHolderSolution
import EllipticPdes.Spectrum.Variational

/-!
# EllipticPdes

Solvability and interior regularity for the linear second-order elliptic Dirichlet
problem in divergence form on a bounded domain, with bounded measurable coefficients
and a drift term, so the bilinear form is in general non-symmetric.

Existence and uniqueness run from the one-dimensional Poincaré inequality through the
domain inequality, continuity and coercivity of the form, and Lax-Milgram. The same
operator then supports the Gårding inequality, the Fredholm alternative with its index
and solvability clauses, the resolvent bound and spectral compactness, the interior
`H²` estimate with its higher-order and smooth refinements, and interior Hölder
continuity in dimensions one to three through Morrey's inequality and Campanato's
characterisation.

Boundary `H²` regularity has its foundations here and its headline estimate open.
-/
