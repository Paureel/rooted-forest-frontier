# Pinned local result and executable consumer

This is an interface specification, not a proof or acceptance claim.
The exact original definitions were read in RMAF.lean lines 84–158 and
PureBridge.lean lines 67–80. Their source hashes are in read-ledger.json.

The local theorem must produce label lists b0,b1 from t,u,b,v, assuming:

- `(leaves t).Nodup` and `(leaves u).Nodup`;
- b nonempty and Nodup, and all its labels occur in both trees;
- `restrictionAgrees t u b = true`;
- v belongs to exact `minimalVertices b t` and has two distinct actual adjacent
  vertices in that induced unsuppressed support.

Its conclusion must include `b0 ≠ []`, `b1 ≠ []`, a permutation
`(b0 ++ b1).Perm b`, disjointness of the blocks, `restrictionAgrees t u bi = true`
for each i, pairwise disjoint exact embeddings in each tree, exact-support
containment in the old b embedding in each tree, and avoidance of v in t.
No hypotheses equating addresses across trees are allowed.

A separately useful, explicitly conditional consumer can start with these
local conclusions and `agreement t u (before ++ b :: after) = true`. It must
prove the unchanged original `agreement t u (before ++ b0 :: b1 :: after) = true`
and exact component-count increment. It may not use a redefined agreement
predicate. The conditional consumer is partial until the local theorem supplies
all its premises from degree two.

The original agreement conjuncts that need preservation are:

1. `partitionCheck (leaves t)` and `partitionCheck (leaves u)`, preserving each
   label's flattened count exactly once and excluding new labels;
2. `all (restrictionAgrees t u)`, requiring actual two-block transport;
3. `pairwiseEmbeddings t` and `pairwiseEmbeddings u`, using both new-block
   disjointness and support containment to retain all other disjoint pieces.

Marks are arbitrary vertex predicates in each tree. Support containment alone
proves preservation of every old avoided mark. New avoidance concerns v in t.
No claim that multiple new marks jointly cost one is licensed; the retained
joint-mark optimum is 1,1,1,2.

For component S to piece b degree transfer, derive minimal support monotonicity
from b subset S and actual leastness. Then prove any occupied nonterminal vertex
in the minimal b support has at least two neighbors. Combined with the degree-two
upper bound from S, this yields degree exactly two in b. Do not treat occupied
subgraph degree as automatically equal to its parent's degree.

G4's at-most-one occupant fact must be connected to the actual list predicate,
with occurrences/indices or nonempty-block uniqueness handled explicitly.
The abstract `ExchangeSystem.clearRest` still quantifies over an entire valid
remainder state: the final trace must identify its exact validity, avoidance and
cost objects, or leave that realization open. G2 and G5–G7 remain outside this
increment even if the local and partition results close.
