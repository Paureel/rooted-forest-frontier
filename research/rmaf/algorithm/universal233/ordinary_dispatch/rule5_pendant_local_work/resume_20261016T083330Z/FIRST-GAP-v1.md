# First remaining Rule5 local statement

Frozen functional source `AdmittedHandler.lean:14-27` evaluates `selectFinal`
and then `runSelected`. This stage covers the former. The first uncovered
body in the first selected arm is

    .prefix s => .answered (runChildren actual T S q (localChildren S a b s))

For `.large e`, `localChildren` first materializes `[pendantChild S a b]`.
`pendantChild` calls `makeChild` on the literal pendant partition, and
`makeChild` evaluates `P.filterMap (fun B => restrict B S)`. The partition and
cut computations are covered here; the literal restriction/materialization
and subsequent `runChildren` bill have not been proved.

The next disjoint source development should implement a structurally recursive
`restrictMeter B S`, prove its value equals `RMAF.restrict B S`, and derive a
concrete source bill such as the conservative candidate

    (restrictMeter B S).work ≤ (2*B.length+6)*(2*(leaves S).length).

That displayed bound is a **pending target**, not an executed theorem. It
must count membership tests, both child traversals, every suppression case,
and result construction on missing and repeated labels before composing
`filterMap`, `makeChild`, `localChildren`, and `runChildren`.

Other selected arms still require their literal source bills: sibling-endpoint
lookup and first/third children, the common source setup/query construction
before the already-sealed common reconstruction, and the second-case paid
source-spine builder/query construction/execution. The actual trace package
supplies callback payload and progress/mass results; it supplies no missing
whole-local cost premise. Root's frozen early-selector interface remains a
separate integration item. `EARLIER-CONSUMER-v1.md` fixes the literal internal
earlierClear contract already proved in this stage.
