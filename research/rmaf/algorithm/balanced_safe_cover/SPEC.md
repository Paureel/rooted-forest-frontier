# Global separator safe-cover specification v1

Source pinned before proof construction: preserved RESEARCH.md §8 lines 234–246; full target in `../SAFE-COVER-TARGET.md`.

## Object and output

Input is an ordinary rooted binary pair (S,T) with exactly the same distinct nonempty label set and integer b≥0. A source-cut certificate is a list of original source edges, a nonempty leaf partition induced by those cuts, the rooted restriction for each component, and its full original support. Empty intermediate vertices do not earn cuts. A valid output has r≤b distinct nonredundant cuts and m=r+1 represented components. Suppressed syntax alone is insufficient to certify the original cuts.

The cover requirement is existential: if Opt(S,T)≤b then there exist an original optimum leaf partition P and a generated F such that P refines the component partition of F. No requirement to preserve every optimum is imposed.

Every F must pass an explicit pure-bridge or compatible/triple recognizer. Pure-bridge outputs must have max_D d(D,T|L_D)≤⌊b/2⌋ for the *unmarked* original output components. The time spent deciding this property is part of generation unless a structural certificate replaces a test.

## MAY-ASSUME

- Finite rooted tree and graph definitions, distinct leaf labels, ordinary no-rho agreement partition definitions.
- Arithmetic identities on component and cut counts, after their stated hypotheses are explicitly checked.
- Conditional consumer statements with their named graph/executable fields treated as parameters: pure-bridge G1–G7; triple G1–G3; exact additional-cut tree–forest solver of base c. These permit conditional implications only.

## MUST-NOT-ASSUME

- Arbitrary approximation or source separator cuts extend to one optimum.
- Independent mark penalties add; a marked budget equals an unmarked local optimum.
- Free tau tests, free local optimization or generation by an optimum oracle.
- The preserved note's 1.94/1.91 products are achieved bounds.
- All-context/all-optima list obstructions refute a one-optimum cover.
- Existing conditional Lean structures supply the missing graph fields.

## Licensed alternative and revision rule

Exact target is generation/size O*((5/4)^b), hardest fraction 1/2. A weaker route is admissible only after a full charged alpha^b,theta certificate with alpha*c^theta<2.3391. Initial candidate numerical alternative: alpha=3/2, theta=1/2 with the classical c=1+sqrt(2), contingent on proving generation bound and every consumer import. This is a preconstruction numerical candidate, not an achieved theorem.

Freeze T1 in `FROZEN-CONTROLS.json`. Any mismatch is a pin erratum with exact witness and append-only revision. Any candidate killed by in-regime exact evidence is retained and replaced by a named distinct organizing route. No finite clean census closes a universal theorem.

## Routes to test after X0

1. GLOBAL-Q: balance via the quotient tree of unknown optimal regions; seek a structural separator certificate that can be enumerated without the unknown optimum.
2. GLOBAL-C: constrained family enumeration using global incompatibility/decomposition certificates; cost exactly the supported candidate outputs and recognition.
3. GLOBAL-W: budget-weighted decision stopping with shared decomposition; prove a total frontier bound including nodes that fail terminal recognition.

This route does not implement the local splitting-core generator explored elsewhere.
