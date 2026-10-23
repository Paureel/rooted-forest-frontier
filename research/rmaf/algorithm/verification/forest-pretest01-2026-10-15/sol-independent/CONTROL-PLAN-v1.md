# Prerelease control plan and hand expectations

Frozen before evaluator execution. JSON tree serialization: a Nat integer is
a leaf; a two-element array is an ordered binary node; JSON null is Option
none. A forest is a list of label lists. Original addresses are strings of
0/1, with the root the empty string. Sibling order is ignored semantically.

## Toolkit decision

Read tools/README.md and searched toolkit/ours/README.md and
toolkit/external/TOOLS.md for graph/partition/forest/Lean/producer capability;
the nearest Gatekeeper and Emitall guides concern numerical oracle gates
and receipt claims, respectively. Neither supplies original-address tree AF
validation or Lean stored-declaration origin/body auditing. Fresh one-shot
problem-local instruments are justified, with retained calibration tests.

## Mathematical routes and exact criteria

A: build an original-address undirected graph, delete original nonroot edges,
read connected leaf components, and validate using graph shortest-path hulls
and induced descendant-cluster topology sets.

B: enumerate all set partitions independently of edge cuts; validate using
recursive restrictions (canonical sibling order), address-LCA path hulls,
and literal full-state label/refinement checks. A and B may share only the
JSON fixture, partition canonicalization for comparison, Python stdlib and
the licensed definition/specification. They have separate tree walks,
topology and hull implementations and no shared validity callback.

Exact equality is required, with no tolerance. Compare every B-valid
cost-at-most-one partition to A's generated valid partitions, not only the
minimum. Compare A's decision to B's global minimum. Check candidate counts
before canonicalization: duplicate partitions count separately.

## Hand-pinned controls

- singleton: T=0, ss=[0], proper, min additional 0, one candidate, found [[0]].
- empty: T=null, ss=[], proper, min 0, one candidate, found [].
- leaf versus empty: T=0, ss=[], malformed/refused.
- empty versus leaf: T=null, ss=[0], malformed/refused.
- mismatch: T=0, ss=[1], malformed/refused.
- duplicate target: T=[0,0], ss=[[0,0]], malformed/refused.
- duplicate source: T=[0,1], ss=[[0,0]], malformed/refused.
- overlapping source labels: T=[0,1], ss=[0,0,1], malformed/refused.
- crossed current forest: T=[[0,1],[2,3]], ss=[[0,2],[1,3]], proper,
  min additional 1, five candidates. Unchanged [[0,2],[1,3]] fails target
  hull disjointness; [[0],[2],[1,3]] is a valid witness with cost 1 and
  ordinary cost 2. Each component's two edge cuts give the same unordered
  partition: four valid candidate entries, two distinct valid partitions.
- crossed single source: same T, ss=[[[0,2],[1,3]]], proper, min additional
  2, seven candidates, cheap rejected; [[0],[1],[2,3]] witnesses cost 2.
  No single cut works: root halves cross in target; isolating a leaf leaves
  an incompatible rooted triple.
- specific coverage: T=[[0,1],2], ss=[[[0,1],2]], proper, min 0, five
  candidates. [[0],[1,2]] is a valid cost-one witness produced only by edge
  00. Deleting edge 00 from the enumerator must fail witness coverage even
  though the unchanged cost-zero optimum survives.
- hidden target vertices: T=[[[0,1],2],[3,4]],
  ss=[[0,3],[1,2],4], proper, min 1, five candidates. The unchanged
  [[0,3],[1,2],[4]] has target-hull intersection at addresses 0 and 00.
  Suppressing unary hull vertices would wrongly accept it at cost 0.
- hidden source vertices: T=[[[0,3],[1,2]],4],
  ss=[[[[0,1],2],[3,4]]]. Witness [[0,3],[1,2],[4]] has disjoint target
  hulls but colliding original source hulls (0 and 00); it must fail.
  This witness's additional cost is 2; no cheap/minimum expectation is
  registered for this extra validator-only control.
- mirrors and source/block/label permutations preserve all decisions,
  costs and normalized valid partitions. Relabel 0..4 to
  [0,17,2^200+19,10^80+7,2^127+1] bijectively and require exact same
  structure; no label-as-index assumption is allowed.

## Deliberate corruption expectations

1. Drop source edge 00 in specific coverage: coverage fails for exactly
   [[0],[1,2]], while the minimum remains zero.
2. Use ordinary |F|-1 instead of prepaid |F|-|ss|: crossed current-forest
   witness reports 2 instead of 1; cost comparator rejects.
3. Omit target hull check: crossed single source wrongly finds cost 1;
   the correct decision comparator rejects this false cheap acceptance.
4. Suppress original unary hull vertices: hidden target witness is wrongly
   accepted; full-hull comparator rejects. A source-only suppressed-hull
   mutation also wrongly accepts hidden source witness; comparator rejects.
5. Root or foreign cut: cut API must refuse; injection of empty cut blocks
   must fail literal partition validation. Clean real-edge twin passes.
6. Duplicated/missing/foreign label, empty block or mixed-source block in
   a candidate: literal partition/refinement check rejects each corruption.
7. Deliberately unequal canonical partition comparison must fail, proving
   the comparison harness fires.

## Producer detector plants (before candidate contact)

Use fresh Lean modules importing only Std: clean theorem/definition; foreign
public axiom; private axiom; unused axiom; a nonproof declaration whose body
mentions an axiom absent from its type; two nonproof definitions with the
same type but different values; and import-order name collision controls.
Record actual stored ConstantInfo kind, type, body, direct constants and
module-origin index before any de-duplication. Transitive body traversal must
detect the hidden axiom. Nonproof definitions must remain distinguishable by
their bodies. Clean twin must pass. Private/unused producers are not erased.

## Pilot, resource plan and debts

Pilot two fixtures, then all hand fixtures only (at most five labels); no
large census. Python subprocess timeout 30 seconds; Lean compile/probe
timeout 60 seconds per command initially, measured and reconsidered only
from retained pilot evidence. Before and after runs require 3 GiB free;
cap new compressed evidence at 256 MiB. Compact JSON/NDJSON and expression
DAGs only; preserve failed/partial output. Scientific progress is completed
fixture/control records, not process liveness.

Candidate source, statements, proof closure, producer origins and use sites
remain unreviewed until exact ROOT-RELEASE. Finite controls cannot establish
universal correctness. Shared reviewer/compiler/Std/runtime trust remains.
Current-component edge cuts do not license global original-cut recovery.
Machine instruction work and bit cost remain separate from candidate count.
All global milestones remain OPEN.
