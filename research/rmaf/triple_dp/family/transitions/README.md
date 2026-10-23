# Universal family-transition increment

This directory holds the universal two-open merge and subsequent live child
restriction work. The existing `../cost_route/FamilyAssembly.lean` covers
close-both and one-sided extension; `../FamilyTransport.lean` maps normalized
families into that indexed model. Those completed sources remain unchanged.

Use this increment when the required step identifies exactly the two child
boundary indices, or when constructing and reindexing actual child families.
Do not use its finite controls to infer optimum values, color legality or
Python solver correctness. `TARGET.md` pins the immediate universal merge;
`../NEXT.md` also states the subsequent restriction obligations.

`controls.json` stores expected supports, label unions, block counts and
closed-region costs written before computation. Malformed inputs must be
rejected; wrong-result and support-corruption twins must be caught while
their clean counterparts pass. A fixture PASS certifies only that finite
comparison. A universal result additionally requires actual Lean family
construction, retained source hashes, standard-axiom queries and false-goal
diagnostics, followed by fresh semantic/control/interface review.

Python runs use `./bootloops-python`; Lean uses the workspace
`./bootloops-lean` with Lean 4.35.0 and workspace `ELAN_HOME`. New build outputs
and receipts must be separate from completed checkpoints. No broad package
suite, extracted implementation or runtime bound follows from a Lean build.

Tool choice: the general BootLoops index has no finite-tree family proof
instrument. The existing family auditor hardcodes its completed source
layers and outputs, so preserving those bytes requires a new incremental
wrapper or direct isolated compiler commands. Existing frozen graph checkers
can support discovery replays; an independent verifier must use a distinct
implementation. Any new checker here is specific to this proof target and
does not replace the toolkit or the existing optimization oracle.
