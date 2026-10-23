# Prerelease cost boundary clarification

Version1, added after the fixed control battery but before candidate contact; no frozen instrument, literal expectation or result was changed. This clarifies how the existing diagnostic dedup controls will be used after release.

Joint-color dedup operates on at most the target's selected leaf count, so a direct quadratic list algorithm can have polynomial input cost. Deduplication of a materialized raw generator-output list can instead see exponentially many records. A quadratic comparison scan there may cost O(4^q), and cannot be hidden in O(poly(input)2^q) merely because raw records have an O(2^q) count. The existing seventeen-distinct-record fixture records136 comparisons to expose this distinction. A released caller must either retain raw outputs, use a proved suitable implementation/bound, or charge the stronger cost. No such choice is inferred before source contact.

The reference instrument's stable-first dedup of raw lists is a diagnostic comparison path, not a required unread candidate transformation and not part of an accepted O(poly(input)2^q) theorem. Candidate value projection must specify whether it returns raw lists, deduplicated colors, deduplicated outputs or a normalized representation. The raw multiplicities and all actual append cells remain accounted regardless. Different exact ordering/equality semantics require an explicit relation and a charged implementation; expectations will not be silently regenerated from candidate outputs.

Likewise the reference canonical local/joint numeric encodings are literal controls for collision/value/bit-length detection, not a predicted candidate encoding. The actual formula and exact asserted bounds must be reviewed after release. Identifier cardinality, value, bit width, callback count and callback work stay separate.

The original fixed34/93 controls and PRE-CANDIDATE-FREEZE remain intact. This clarification introduces no new test result, candidate source input or independent replication. All three main milestones OPEN.
