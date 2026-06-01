/-!
# One-dimensional Poincaré inequality (dependency-chain step 1)

For a compactly supported `u` on an interval, the `L²` norm of `u` is bounded by
a constant times the `L²` norm of `u'`. Proof: fundamental theorem of calculus,
then Cauchy-Schwarz. This is the first standalone Mathlib pull request (M2).
-/
import Mathlib

namespace EllipticDirichlet.Poincare

-- TODO(M2): state and prove the one-dimensional Poincaré inequality.
-- Target shape: for `u : ℝ → ℝ` compactly supported in `(a, b)`,
--   `∫ x in a..b, (u x)^2 ≤ C * ∫ x in a..b, (deriv u x)^2`  with `C = (b-a)^2 / 2` (or sharp).

end EllipticDirichlet.Poincare
