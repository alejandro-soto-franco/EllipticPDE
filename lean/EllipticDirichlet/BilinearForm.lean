import Mathlib
import EllipticDirichlet.Poincare.Density
import EllipticDirichlet.Sobolev.Basic

/-!
# The divergence-form bilinear form (dependency-chain step 5)

`B[u, v] = ∫_Ω (A ∇u · ∇v + c u v)`. Uniform ellipticity plus the Poincaré
inequality give the coercivity constant `α`; bounded coefficients give the
continuity constant `β`. Both are mirrored in the Rust numerics (Rayleigh
quotients of the assembled stiffness form); see `docs/.../notes/constants.md`.
-/

namespace EllipticDirichlet

-- TODO(M5): define `B`, prove continuity (β) and coercivity (α).

end EllipticDirichlet
