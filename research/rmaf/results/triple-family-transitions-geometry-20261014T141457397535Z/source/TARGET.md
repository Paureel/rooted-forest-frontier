# Universal merge target — 2026-10-14

Regime 1: a fixed universal statement, derived from the already reviewed
`../NEXT.md`. This target is OPEN until the adversary, kernel proof and fresh
semantic/control/interface review complete.

Given finite binary trees l and r, actual `CostRoute.Family l I` and
`CostRoute.Family r J`, and designated i,j with boundary equal to `some i`
and `some j`, construct an actual family on `BTree.node l r`. Every index
other than i or j survives separately. Exactly those two indices become one
new boundary index. Its support is the parent root together with the lifted
supports of i and j. All other supports are lifted unchanged.

Prove all output fields: complete duplicate-free finite indexing, bounded
convex supports, a leaf in every support, pairwise disjointness, coverage of
all leaves, and exact root/boundary ownership. Prove exact per-index leaf
preservation and union of the merged leaf blocks. Prove count
`L.blockCount + R.blockCount - 1` and cost `L.cost + R.cost`.

MAY ASSUME: unchanged audited `TripleDP`, `ConnectedRegions`, `PathStem`,
`FamilyModel`, `FamilyTrim`, `FamilyGeometry`, `FamilyAssembly`, and
`FamilyTransport`, with their actual hypotheses. Import only what the proof
needs and rebuild local imports in an isolated directory. The existing
finite-index and family definitions are shared semantics.

MUST NOT ASSUME: the desired merge family, its count/cost/leaf correspondence,
child restriction/reindexing, complete four-transition correspondence,
color/mask admissibility, executable graph correspondence, or Python
correctness. `normalized_assembly_exists` exports no support equality.

Acceptance is the actual construction and its universal equations, together
with executed frozen controls, actual false-proposition diagnostics and clean
twins, a standard-axiom audit, and fresh nonauthor review. If a control finds
an in-regime counterexample, retain it exactly and correct the target before
proving. Out-of-regime malformed families are rejection controls, not
counterexamples. A partial geometric or indexing lemma may be retained with
its missing consuming interfaces explicit; it does not close merge.

Frozen fixture convention: root is the empty string, left edge is 0, right
edge is 1, and a string tree value is a leaf label. Index names are distinct
even when color fields agree. The expected merged indices are M, L:<index>,
and R:<index>. The controls pin exact supports and counts independently of
any computed construction. T1 is two open singleton children: output one
block, closed cost zero, support {root,0,1}. Claims of two blocks or cost one
must fail; their exact correct twins must pass.

Later restriction work must receive its own frozen controls before new
construction. It must select/reindex only live fragments and account for a
parent closed region becoming a child boundary. Full G2 remains OPEN after
merge until that universal reverse direction and other stated links exist.
