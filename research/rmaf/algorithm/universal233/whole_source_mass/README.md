# Whole-source original-label colors and raw generator mass

This package proves exact original input color cardinalities and consumes the
actual whole-source generator for the clique, four-chain, and count-two
diagonal mass bounds. The full faster rooted-MAF algorithm remains OPEN.
The result has an author kernel check; independent nonauthor review is pending.

From the workspace root:

    ./bootloops-python research/rmaf/algorithm/universal233/whole_source_mass/replay.py

The replay copies all proof sources into a fresh
`results/algorithm-universal233-whole-mass-*` directory and compiles those
copies with `./bootloops-lean`. It verifies the 140-file frozen source-coverage
manifest, inventories every declaration originating in its 29 imported proof
modules, checks their axiom dependencies, and runs true, false and corrupted
audit controls. The receipt states the module counts, source hashes, measured
build times, controls, and remaining consumer. A successful replay means that
Lean accepted these conditional mass theorems with the permitted standard
axioms; it does not mean that the complete algorithm was proved.

| Module | Result |
|---|---|
| WholeColors | Exact tagged input cardinality from literal source parent membership |
| OriginalColors | Exact original-label region and joint-region cardinalities |
| WholeMass | Actual appended generator output lists and three mass bounds |
| MassControls | Concrete clique, count-three chain, count-two diagonal, root, empty-parent and multiplicity controls |

This is a problem-specific instrument. The toolkit capability index and frozen
generator replay were consulted; the existing generator mass theorem was
reused, while the missing original-label cardinality bridge was written here.
Reach for this package when composing the public whole-source ownership
construction. Source coverage, original cuts, and whole-algorithm assembly
have separate interfaces. `RESULT.md` lists the exact hypotheses and
`FIRST-GAP.md` states the first remaining consumer.

The positive fixture calls go through literal `CoreProgram.generate` output
lists. Four false Lean propositions must fail, and source-pin, missing-audit-
record, and private-custom-axiom plants must be rejected. The controls and
their clean twins are retained in each receipt. The initial audit failure is
preserved separately; see `WORKFILE.md`.
