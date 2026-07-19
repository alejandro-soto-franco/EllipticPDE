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
import EllipticPdes.Regularity.CutoffTower
import EllipticPdes.Regularity.RestrictedDiffQuotient
import EllipticPdes.Regularity.RestrictedDiffQuotientMem
import EllipticPdes.Regularity.Interior
import EllipticPdes.Regularity.DifferentiatedEquation
import EllipticPdes.Embedding.WeakGradient
import EllipticPdes.Embedding.Convolution
import EllipticPdes.Embedding.MorreyOneDim
import EllipticPdes.Embedding.RayIntegral
import EllipticPdes.Embedding.Morrey
import EllipticPdes.Embedding.WeakDerivBridge
import EllipticPdes.Fredholm.Fredholm
import EllipticPdes.Fredholm.FredholmComplete
import EllipticPdes.Spectrum.SpectrumSigma
import EllipticPdes.Fredholm.Compactness
import EllipticPdes.Spectrum.Spectrum
import EllipticPdes.Spectrum.RellichDischarge
import EllipticPdes.BoundedInstances

/-!
# EllipticPdes

Existence and uniqueness for the linear elliptic Dirichlet problem, assembled
from a Sobolev layer, the Poincaré inequality, and the Lax-Milgram theorem.

See `docs/superpowers/specs/2026-06-01-elliptic-dirichlet-existence-design.md`
in the planning repository for the full design and the dependency chain.
-/
