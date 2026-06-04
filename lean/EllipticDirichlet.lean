import EllipticDirichlet.Sobolev.Basic
import EllipticDirichlet.Sobolev.Coefficients
import EllipticDirichlet.Poincare.OneDim
import EllipticDirichlet.Poincare.Fubini
import EllipticDirichlet.Poincare.Domain
import EllipticDirichlet.Poincare.Density
import EllipticDirichlet.Poincare.Geometry
import EllipticDirichlet.Poincare.BoxSlice
import EllipticDirichlet.BilinearForm
import EllipticDirichlet.Existence
import EllipticDirichlet.GeneralForm
import EllipticDirichlet.Garding
import EllipticDirichlet.Fredholm
import EllipticDirichlet.Compactness
import EllipticDirichlet.Spectrum

/-!
# EllipticDirichlet

Existence and uniqueness for the linear elliptic Dirichlet problem, assembled
from a Sobolev layer, the Poincaré inequality, and the Lax-Milgram theorem.

See `docs/superpowers/specs/2026-06-01-elliptic-dirichlet-existence-design.md`
in the planning repository for the full design and the dependency chain.
-/
