import Mathlib

/-!
# Sobolev interface

The `H¹ / H₀¹` interface this project needs: thin wrappers or re-exports over
what Mathlib (`MeasureTheory.MemWlp`) and the De Giorgi-Nash-Moser Sobolev layer
already provide. The exact delta is fixed by the audit
(`docs/superpowers/notes/sobolev-poincare-audit.md`, milestone M1).
-/

namespace EllipticDirichlet.Sobolev

-- TODO(M1/M2): pin down the H₀¹ interface over Mathlib `MemWlp` after the audit.

end EllipticDirichlet.Sobolev
