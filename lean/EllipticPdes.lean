/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Sobolev.Basic
public import EllipticPdes.Sobolev.Coefficients
public import EllipticPdes.Regularity.DifferenceQuotient
public import EllipticPdes.Regularity.DiffQuotientBound
public import EllipticPdes.Poincare.OneDim
public import EllipticPdes.Poincare.Domain
public import EllipticPdes.Poincare.Density
public import EllipticPdes.Poincare.Geometry
public import EllipticPdes.Poincare.BoxSlice
public import EllipticPdes.Poincare.BoundedDomain
public import EllipticPdes.Form.BilinearForm
public import EllipticPdes.Form.Hneg
public import EllipticPdes.Existence.Existence
public import EllipticPdes.Form.GeneralForm
public import EllipticPdes.Existence.Garding
public import EllipticPdes.Regularity.Caccioppoli
public import EllipticPdes.Regularity.InteriorCompactSupport
public import EllipticPdes.Regularity.CoeffC1
public import EllipticPdes.Regularity.CoeffLip
public import EllipticPdes.Regularity.CoeffLipWeakGrad
public import EllipticPdes.Regularity.CoeffC2
public import EllipticPdes.Regularity.CoeffCk
public import EllipticPdes.Regularity.CoeffWkInfty
public import EllipticPdes.Regularity.CoeffBridge
public import EllipticPdes.Regularity.MollifyWkInfty
public import EllipticPdes.Regularity.LowerOrderWkInfty
public import EllipticPdes.Regularity.CutoffTower
public import EllipticPdes.Regularity.RestrictedDiffQuotient
public import EllipticPdes.Regularity.RestrictedDiffQuotientMem
public import EllipticPdes.Regularity.Interior.Support
public import EllipticPdes.Regularity.Interior.EnergyBound
public import EllipticPdes.Regularity.Interior.NormBound
public import EllipticPdes.Regularity.Interior
public import EllipticPdes.Regularity.LeibnizWkInfty
public import EllipticPdes.Regularity.DifferentiatedWkInfty
public import EllipticPdes.Regularity.LocalWeakFormWkInfty
public import EllipticPdes.Regularity.WeakFormDense
public import EllipticPdes.Regularity.HigherWeakDeriv
public import EllipticPdes.Regularity.MulIterated
public import EllipticPdes.Regularity.IteratedSum
public import EllipticPdes.Regularity.IteratedRestrict
public import EllipticPdes.Regularity.L2Pairing
public import EllipticPdes.Regularity.ExtendCutoff
public import EllipticPdes.Regularity.WeakDerivOnSymm
public import EllipticPdes.Regularity.CutoffGradFormula
public import EllipticPdes.Regularity.CollarIdentify
public import EllipticPdes.Regularity.CutoffCommutator
public import EllipticPdes.Regularity.DatumPiece
public import EllipticPdes.Regularity.CutoffDatum
public import EllipticPdes.Regularity.SmoothGlue
public import EllipticPdes.Regularity.HigherInterior
public import EllipticPdes.Regularity.IteratedFamily
public import EllipticPdes.Regularity.InteriorSmooth
public import EllipticPdes.Regularity.InteriorSmoothGlobal
public import EllipticPdes.Regularity.Localise.CutoffProduct
public import EllipticPdes.Regularity.Localise.LocalOp
public import EllipticPdes.Regularity.Localise.Datum
public import EllipticPdes.Regularity.Local.WeakSolution
public import EllipticPdes.Regularity.Local.Reduction
public import EllipticPdes.Regularity.Local.Caccioppoli
public import EllipticPdes.Regularity.Local.InteriorH2
public import EllipticPdes.Regularity.Local.Datum
public import EllipticPdes.Regularity.Local.HigherInterior
public import EllipticPdes.Regularity.Local.InteriorSmooth
public import EllipticPdes.Regularity.Local.Evans
public import EllipticPdes.Regularity.Localise.FiniteOrder
public import EllipticPdes.Regularity.IteratedNorm
public import EllipticPdes.Regularity.Local.Classical
public import EllipticPdes.Regularity.ClassicalSolvability
public import EllipticPdes.Regularity.PointwiseEquation
public import EllipticPdes.Regularity.InteriorHolderFinite
public import EllipticPdes.Regularity.DifferentiatedEquation
public import EllipticPdes.Regularity.Boundary.HalfBall
public import EllipticPdes.Regularity.Boundary.TangentialDiffQuotient
public import EllipticPdes.Regularity.Boundary.TangentialDiffQuotientMem
public import EllipticPdes.Regularity.Boundary.WeakQuotientRule
public import EllipticPdes.Regularity.WeakLimit
public import EllipticPdes.Regularity.CutoffDeriv
public import EllipticPdes.Regularity.WeakDerivUnique
public import EllipticPdes.Regularity.TestFnCut
public import EllipticPdes.Regularity.OuterCutoffTower
public import EllipticPdes.Regularity.LocalWeakForm
public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Embedding.Convolution
public import EllipticPdes.Embedding.RayIntegral
public import EllipticPdes.Embedding.Morrey
public import EllipticPdes.Embedding.WeakDerivBridge
public import EllipticPdes.Campanato.Basic
public import EllipticPdes.Campanato.Compare
public import EllipticPdes.Campanato.Telescope
public import EllipticPdes.Campanato.Holder
public import EllipticPdes.Campanato.Converse
public import EllipticPdes.Embedding.WeakSobolev
public import EllipticPdes.Embedding.GagliardoNirenberg
public import EllipticPdes.Embedding.SobolevLadder
public import EllipticPdes.Embedding.SobolevLadderCompactSupport
public import EllipticPdes.Embedding.HolderGeneral
public import EllipticPdes.Extension.C1Test
public import EllipticPdes.Extension.Cutoff
public import EllipticPdes.Extension.HalfSpace
public import EllipticPdes.Extension.EvenReflection
public import EllipticPdes.Extension.Shear
public import EllipticPdes.Extension.ShearWeakGrad
public import EllipticPdes.Extension.BoundaryChart
public import EllipticPdes.Extension.C1Boundary
public import EllipticPdes.Extension.BallChart
public import EllipticPdes.Extension.Motion
public import EllipticPdes.Extension.Patch
public import EllipticPdes.Extension.PartitionOfUnity
public import EllipticPdes.Extension.LocalExtension
public import EllipticPdes.Extension.Operator
public import EllipticPdes.Extension.LinearOperator
public import EllipticPdes.Extension.GlobalApproximation
public import EllipticPdes.Extension.GraphOperator
public import EllipticPdes.Extension.Reflect
public import EllipticPdes.Extension.Translate
public import EllipticPdes.Analysis.LpTranslationContinuity
public import EllipticPdes.Extension.ShiftMollify
public import EllipticPdes.Embedding.WeakGradUnique
public import EllipticPdes.Embedding.ClassicalDeriv
public import EllipticPdes.Embedding.SmoothOfGradClosed
public import EllipticPdes.Embedding.HolderOfGradClosed
public import EllipticPdes.Embedding.InteriorHolder
public import EllipticPdes.Embedding.DomainSobolev
public import EllipticPdes.Embedding.DomainLadder
public import EllipticPdes.Embedding.DomainHolder
public import EllipticPdes.Embedding.DomainSmooth
public import EllipticPdes.Embedding.SobolevEmbedding
public import EllipticPdes.Fredholm.CompactOperator
public import EllipticPdes.Fredholm.Fredholm
public import EllipticPdes.Fredholm.FredholmComplete
public import EllipticPdes.Fredholm.GardingForm
public import EllipticPdes.Spectrum.CompactSpectrum
public import EllipticPdes.Spectrum.GardingSigma
public import EllipticPdes.Spectrum.SpectrumSigma
public import EllipticPdes.Fredholm.Compactness
public import EllipticPdes.Spectrum.Spectrum
public import EllipticPdes.Spectrum.RellichDischarge
public import EllipticPdes.BoundedInstances
public import EllipticPdes.Analysis.WeakCompactness
public import EllipticPdes.Analysis.DirectMethodForm
public import EllipticPdes.Analysis.LpInterpolation
public import EllipticPdes.Analysis.Dilation
public import EllipticPdes.Analysis.SmoothCutoff
public import EllipticPdes.Analysis.Mollifier
public import EllipticPdes.Embedding.H01Sobolev
public import EllipticPdes.Embedding.SobolevSolution
public import EllipticPdes.Embedding.RellichLq
public import EllipticPdes.Embedding.SobolevSharp
public import EllipticPdes.Analysis.LqDerivative
public import EllipticPdes.Analysis.LqEulerLagrange
public import EllipticPdes.Embedding.DirectMethod
public import EllipticPdes.Embedding.DirichletSemilinear
public import EllipticPdes.Regularity.InteriorHolderSolution
public import EllipticPdes.Spectrum.Variational
public import EllipticPdes.Spectrum.HigherEigenvalues
public import EllipticPdes.Spectrum.EigenFamily
public import EllipticPdes.Spectrum.Multiplicity
public import EllipticPdes.Spectrum.BallDimension
public import EllipticPdes.Embedding.ConstOfGradZero
public import EllipticPdes.Spectrum.RellichW12
public import EllipticPdes.Spectrum.PoincareWirtinger
public import EllipticPdes.Spectrum.PoincareBall
public import EllipticPdes.Embedding.WeakDerivChain
public import EllipticPdes.Embedding.ChainRule
public import EllipticPdes.Existence.WeakMaximum
public import EllipticPdes.Sobolev.H01Lattice
public import EllipticPdes.Embedding.H01SobolevTwo
public import EllipticPdes.Existence.WeakMaximumTransport
public import EllipticPdes.Existence.ClassicalMaximum
public import EllipticPdes.Existence.StrongMaximum
public import EllipticPdes.Existence.StrongMaximumCorollaries
public import EllipticPdes.Existence.AprioriBound
public import EllipticPdes.Existence.Harmonic
public import EllipticPdes.Analysis.EuclideanFunctionalNorm
public import EllipticPdes.Analysis.FrechetKolmogorov
public import EllipticPdes.Analysis.LpExtendByZero
public import EllipticPdes.Analysis.LpTranslation
public import EllipticPdes.Analysis.PoincareInequality
public import EllipticPdes.Analysis.Translation
public import EllipticPdes.Extension.Basic
public import EllipticPdes.Extension.Descent
public import EllipticPdes.Poincare.Slab
public import EllipticPdes.Sobolev.Graph
public import EllipticPdes.Form.DivForm
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Sobolev.GraphLimits
public import EllipticPdes.Sobolev.WeakDeriv
public import EllipticPdes.Sobolev.WeakDerivClassical

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

@[expose] public section
