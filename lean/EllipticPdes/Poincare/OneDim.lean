/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

module

public import EllipticPdes.Analysis.PoincareInequality

/-!
# One-dimensional Poincaré inequality

Aliases of the declarations of `EllipticPdes.Analysis.PoincareInequality` in the
`EllipticPdes.Poincare` namespace.

* `intervalIntegral_mul_sq_le`: Cauchy-Schwarz for `∫ f g`.
* `sq_intervalIntegral_le`: the `g = 1` special case.
* `poincare_oneDim`: the one-dimensional Poincaré inequality.
-/

@[expose] public section

namespace EllipticPdes.Poincare

alias intervalIntegral_mul_sq_le := EllipticPdes.Analysis.intervalIntegral_mul_sq_le
alias sq_intervalIntegral_le     := EllipticPdes.Analysis.sq_intervalIntegral_le
alias poincare_oneDim            := EllipticPdes.Analysis.poincare_1d

end EllipticPdes.Poincare
