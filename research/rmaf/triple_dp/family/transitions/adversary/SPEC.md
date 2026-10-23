# Independent finite merge checker specification

Pinned before reading any Lean definitions or author checker. Exact finite
arithmetic only. This is an adversarial bounded instrument, not a proof.

## Read sources

TARGET.md paragraphs 2–3 require separately retained indices, exact supports,
all family fields, per-index leaf preservation, count sum−1 and cost sum.
NEXT.md section “Merge the two distinguished open indices” states:
“The output is geometrically a family regardless of colors; whether a DP
rule permits the merged label block is a separate admissibility obligation.”
TARGET.md's fixture convention fixes binary string addresses and live child
boundaries. No existing checker or proof code has been read.

## Route G: undirected graph

Recursively traverse the JSON binary tree into an undirected adjacency list.
Every explicit index must occur exactly once in a finite index list and have
exactly one support. Every support must lie in the tree, contain a leaf, and
contain every vertex on the unique BFS path between every pair of its nodes.
Supports must be disjoint; every leaf must have exactly one owner. The root
belongs to precisely the boundary index if that index exists, and to no
index if boundary is absent. Absent boundaries define valid families but are
invalid merge inputs.

Construct candidate supports by prefixing left addresses with 0 and right
addresses with 1, deleting only the designated boundary indices and inserting
M with their lifted union and the parent root. Use tagged textual output
indices M, L:<name>, R:<name>. Count is number of explicit indices; cost is
number of indices unequal to boundary. Check the output family afresh, exact
surviving and merged support equality, exact leaf-node sets, and label sets.

## Route P: separate prefix/owner method

Implement tree decoding, vertex ownership, root ownership, leaf coverage,
and convexity separately without calling Route G functions. Construct the
required output by scanning parent vertices and assigning their owners from
child owners. Compute block count and closed cost from distinct leaf-owner
classes; this is justified only after each index is checked leaf-bearing.
Convexity checks all prefixes back to the pair's common prefix, with no BFS.
The deepest shared layers are the frozen specification, literal fixtures,
Python standard library and this author. This is algorithmic cross-checking,
not fresh-author certification.

## Failure semantics and controls

All equality checks are exact. Wrong numeric claims must emit claimed,
actual, and signed residual; clean twins pass. Support corruptions must fail
with structural diagnostics and a clean twin must pass. Corrupted numeric
checker copy must cause battery failure before bounded hunt.
Malformed inputs never become theorem counterexamples. Any disagreement
between routes stops as CHECKER-DISAGREEMENT; any merge failure after both
routes certify valid live-boundary input stops as FIRE and saves the full
exact input/output/diagnostic witness. Neither is silently relabeled.

## Bounded search and pilot

Enumerate all set partitions of the vertices plus an unowned class, require
all leaves owned, require root owned, then retain only actual valid families.
Canonical index names represent partitions up to index renaming; no color
restriction. Cover leaf, cherry and the two oriented three-leaf combs only.
Main pairs have total leaves ≤5 and each child ≤3 leaves. Thus the largest
child has five vertices and the largest parent nine vertices. Input family
enumeration is independent of the target merger. The pilot runs the same
candidate generation and merger on a deterministic at-most-16-pair slice
from every planned tree pair; main proceeds only after its measured bound is
recorded. The main receipt records denominators, elapsed time, hashes and
exact failure records. Stop at first in-regime failure; never enlarge search
because a NO-FIRE is unsatisfying.

## Tool choice

The complete bootloops/tools/README.md catalog has been read. Its graph
packages (dogtag, geotriage, cosmoflow) address integral topology or geometry,
not finite indexed convex region families, while emitall audits receipts.
A new isolated problem-specific checker is required by this arm's no-reuse
contract; none of those tools supplies the specified independent graph/path
family semantics. No upstream toolkit code is changed.
