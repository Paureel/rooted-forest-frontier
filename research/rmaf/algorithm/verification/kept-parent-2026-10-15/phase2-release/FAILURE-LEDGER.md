# Retained released-review failures

1. The first fresh source driver also tried frozen CheckAPI.lean, an unimported declaration-free development API probe outside the canonical 41-module certificate. It failed four old #check names. Canonical 41 modules, LiteralControls and Interfaces compile. The probe source/log and partial v1 receipt are retained; its contents were not repaired or counted as an accepted positive module.

2. The first literal #print axioms file concatenated full private names as parser text. Numeric components such as _private.Branches.0 are not accepted in that textual syntax. Full originating axiom closures and the second environment traversal had already succeeded. Preserve FreshPrintedAxioms.lean/log. The corrected printer constructs Lean Name values with their string/numeric components and emits #print axioms via mkIdent/elabCommand, without dropping private/generated theorems.

The preparation's two earlier failures and versioned corrections remain immutable in the parent readiness freeze. None of these failures is treated as a mathematical rejection or a passing control. No author source was edited.
