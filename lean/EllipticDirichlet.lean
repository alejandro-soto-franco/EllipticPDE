/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
import EllipticDirichlet.Sobolev.Basic
import EllipticDirichlet.Sobolev.Coefficients
import EllipticDirichlet.Regularity.DifferenceQuotient
import EllipticDirichlet.Regularity.DiffQuotientBound
import EllipticDirichlet.Poincare.OneDim
import EllipticDirichlet.Poincare.Fubini
import EllipticDirichlet.Poincare.Domain
import EllipticDirichlet.Poincare.Density
import EllipticDirichlet.Poincare.Geometry
import EllipticDirichlet.Poincare.BoxSlice
import EllipticDirichlet.Poincare.BoundedDomain
import EllipticDirichlet.BilinearForm
import EllipticDirichlet.Hneg
import EllipticDirichlet.Existence
import EllipticDirichlet.GeneralForm
import EllipticDirichlet.Garding
import EllipticDirichlet.Regularity.Caccioppoli
import EllipticDirichlet.Regularity.InteriorCompactSupport
import EllipticDirichlet.Regularity.CoeffC1
import EllipticDirichlet.Regularity.CutoffTower
import EllipticDirichlet.Regularity.RestrictedDiffQuotient
import EllipticDirichlet.Regularity.RestrictedDiffQuotientMem
import EllipticDirichlet.Regularity.Interior
import EllipticDirichlet.Embedding.WeakGradient
import EllipticDirichlet.Fredholm
import EllipticDirichlet.FredholmComplete
import EllipticDirichlet.SpectrumSigma
import EllipticDirichlet.Compactness
import EllipticDirichlet.Spectrum
import EllipticDirichlet.RellichDischarge
import EllipticDirichlet.BoundedInstances

/-!
# EllipticDirichlet

Existence and uniqueness for the linear elliptic Dirichlet problem, assembled
from a Sobolev layer, the Poincaré inequality, and the Lax-Milgram theorem.

See `docs/superpowers/specs/2026-06-01-elliptic-dirichlet-existence-design.md`
in the planning repository for the full design and the dependency chain.
-/
