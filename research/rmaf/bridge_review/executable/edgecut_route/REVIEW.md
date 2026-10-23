# Fresh edge-cut route review

Date: 2026-10-14. Status: all 12 frozen controls reproduced; three corrupted
supports rejected for semantic falsehood. The complete formal interface remains
outside this arm's certification.

## Target and permissions

Read `../../EXECUTABLE-TARGET.md` first. Prove/check the exact nonempty
`minimalVertices` connectivity interface. No leastness, unique-label semantics,
or restriction-transport closure is claimed. This arm will not read candidate
`ExecutableConnectivity.lean`, `GraphRegion` proof bodies, other reviews, or
existing Python checkers. The named independent route builds the finite tree
graph, removes each edge, and selects precisely edges whose two components both
contain selected leaf occurrences; a singleton occurrence contributes its vertex.

## Frozen controls and failure conditions

`frozen-controls.json` is authored from the target and hand graph reasoning,
before reading RMAF. Tree leaves are integers; binary nodes are pairs. Vertices
are root-to-node bit strings (0=false/left, 1=true/right, empty=root). Support is
a set, independently of list ordering. Every mismatch is a failure. Deleting
vertex `0` from the quartet cross support must be rejected as disconnected and
as unequal support. Suppressed initial paths must remain absent. Duplicate
labels mean selected occurrences, not a single representative.

## Toolkit decision

The toolkit index was read. No package supplies a Lean binary-tree hull or a
finite edge-deletion certificate. This is a one-shot, problem-specific exact
checker; new code is restricted to this directory and will not copy any existing
checker. Python exact integer/set operations and the installed Lean kernel are
the engines. No numerical approximation or large scan is planned.

## Source ledger

Read: `research/rmaf/lean/RMAF.lean`, SHA-256
`4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`.
Opened lines 1–14 and 104–135, including the imports, Tree definition, and
executable support definitions; a preceding declaration-name search listed
the module's definition headers. The whole unchanged module was compiled as a
dependency. No candidate theorem or existing checker was opened.

Read, lines 111–112: `vs.map (side :: ·)` defines `prependSide`. Lines 116–122
define `rootedSpan`; the nonempty node branch is exactly
`else [] :: (prependSide false ls ++ prependSide true rs)`.
Lines 126–133 define `minimalVertices`; its node cases are exactly:

```lean
if ls.isEmpty then prependSide true (minimalVertices selected r)
else if rs.isEmpty then prependSide false (minimalVertices selected l)
else [] :: (prependSide false ls ++ prependSide true rs)
```

Read, lines 117 and 127: a selected leaf returns `[[]]`, otherwise `[]`.
Inference: labels need not be unique for this recursion; selection tests each
leaf occurrence independently. `duplicate_siblings` and `duplicate_cross`
execute that inference directly. No source/spec disagreement occurred.

Read after the controls completed: only lines 9–14 of
`research/rmaf/bridge_review/lean/GraphRegion.lean`, SHA-256
`5d53cadd43f7c654656040218939c2051f8592e5045227bc2506dd2cddee5455`.
The declarations are:

```lean
def Adj (u v : Address) : Prop :=
  (∃ b : Bool, v = u ++ [b]) ∨ (∃ b : Bool, u = v ++ [b])

inductive Walk (P : Address → Prop) : Address → Address → Prop
  | refl {x} : P x → Walk P x x
  | step {x y z} : Walk P x y → Adj y z → P z → Walk P x z
```

No GraphRegion proof body was opened. Reading these declarations confirms that
the explicit graph's parent–child edges are exactly `Adj` restricted to actual
tree vertices. Every finite graph path inside a support yields its corresponding
membership-predicate `Walk` by the
membership-bearing `refl` followed by its `step` constructor. A singleton uses
`refl` alone; an empty support cannot supply that membership proof.

## Derivation

Let G be the finite undirected graph with one vertex per node occurrence of the
binary tree and an edge between each parent and child. Let T be the set of leaf
occurrences whose labels belong to S. Define H to contain T and the endpoints
of every edge e for which both components of G minus e contain a member of T.
The checker constructs the graph with a stack, deletes each edge, and finds
components by graph search; it never implements the executable support
recursion.

For distinct a,b in T, an edge e lies on their unique tree path exactly when a
and b lie in opposite components of G minus e. Consequently every a–b path is
contained in H, and every selected edge lies on such a path. If T is nonempty,
fix t in T. For each vertex v of H, either v is a terminal or v lies on a path
between terminals a and b. In the latter case the union of that path and the
path from a to t connects v to t using only selected edges. Thus H is connected.
If T has one element, no edge qualifies and H is its one vertex. If T is empty,
H is empty. These statements use occurrences, so repeated labels cause no
exception.

The correspondence with the read executable definitions follows by structural
induction. First, `rootedSpan` is empty exactly when the subtree contains no
selected occurrence. Otherwise its vertices are precisely the union of paths
from that subtree's root to its selected occurrences: the leaf case is direct,
and the node branch inserts its root and prefixes both child spans.

For `minimalVertices`, if both child terminal sets are nonempty, an edge within
either child qualifies exactly when its descendant side contains a selected
terminal. The opposite child supplies a terminal on the other side of the cut.
The two child-root edges qualify too. H is therefore the node root together
with the two prefixed rooted spans, exactly the third executable branch. If
only one child contains selected terminals, the edge to that child does not
qualify: the other cut component has no selected terminal. Every qualifying
edge is internal to that child's H, matching the relevant recursive branch.
If neither child contributes, both the recursive output and H are empty. The
leaf case gives a singleton exactly when the label is selected. This proves
the set-level correspondence in ordinary mathematics and the nonempty
connectivity conclusion. This arm does not contain a Lean formalization of
that universal edge-cut correspondence.

## Executed evidence

The fresh script is `edgecut_check.py`. Run it from the workspace root:

```text
./bootloops-python research/rmaf/bridge_review/executable/edgecut_route/edgecut_check.py graph
./bootloops-python research/rmaf/bridge_review/executable/edgecut_route/edgecut_check.py lean
```

`graph-results.json` retains all 12 exact supports and every edge's terminal
split. Its first run recovered 12/12 hand plants and caught 3/3 corruptions in
0.00031762500111653935 seconds. The empty-selection and absent-label plants
returned empty supports. A duplicated entry in S had no effect, while a
duplicated leaf label selected every occurrence.

The Lean phase freshly compiled unchanged RMAF into this folder before import.
Lean version: 4.35.0, arm64-apple-darwin24.6.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Each positive example uses `by decide`
on exact bidirectional list membership. The actual support printed by `#eval`
then matches the Python edge-cut set. No `native_decide` or placeholder
is used in the authored Lean controls.

The successful rerun timings are in `lean-results.json`: dependency rebuild
5.589257333000205 seconds; one-leaf pilot 0.30213874999935797 seconds; all 12
positive examples 0.3829594580001867 seconds. No enumeration ran. The 12-case
batch had a 60-second timeout; `launch-plan.json` records the measured pilot and
bounded batch before its launch, without extrapolating a rate from startup.

Exact control output, excerpt from `exact-controls.log`:

```text
duplicate_siblings	["", "0", "1"]
duplicate_cross	["", "0", "00", "1", "10"]
suppressed_initial_path	["11", "110", "111"]
suppressed_single_path	["11"]
repeated_selection	["00"]
```

All three false equality examples reached Lean's semantic decision procedure
and failed there. For the deleted path vertex, the retained diagnostic is:

```text
error: Tactic `decide` proved that the proposition
  sameSupport (minimalVertices [0, 2] quartet_cross) [[], [false, false], [true], [true, false]] = true
is false
```

The exact first line includes a file/line location in
`false-deleted_path_vertex.log`; the excerpt above omits that location. In
addition, Python found the corrupted induced support disconnected. The other
false controls add the suppressed input root or discard a duplicate selected
occurrence. Those two supports are connected, so their rejection specifically
demonstrates support-equality checking beyond a connectivity-only test.

An initial diagnostic parser expected the words `evaluated to false`; Lean
instead printed the semantic falsehood diagnostic quoted above. That initial
run stopped at the parser assertion, after its positive tests had passed. Its
script, logs and timers remain in `attempt1/`. The only correction accepts the
observed explicit `Tactic decide ... is false` wording, retaining checks against
unknown identifiers and type errors. The Lean tests were then rerun. This was a
diagnostic-format mismatch; no expected support or mathematical condition was
changed.

Final script output, verbatim:

```text
PASS: 12/12 exact edge-cut/source support matches; 3/3 semantic false controls rejected.
```

## Lineage and contact log

Hand controls: author this fresh agent; inputs target plus named distinct route;
accuracy exact finite graph sets; creation before source inspection. They are
not generated by extractor code. Comparator contact starts only after freeze.
Shared layer with candidate: target statement, binary-tree input convention,
and eventual unchanged RMAF definitions; no candidate proof or code contact.

The controls' SHA-256 is
`d4f251ce0cdf7de4984b44a4024629c1be3d08518f84c79691eab977504f838b`.
The Python construction and the Lean extractor share no support-building code.
They share the finite tree input, left/right encoding, and selected labels; a
wrong shared input could affect both. The controls were hand-authored before
the RMAF source was opened, which addresses extraction-recurrence errors but
does not independently certify the target's tree convention. The first five
supports were specified by the target; the remaining seven were independently
hand-derived from the explicit tree graph before source contact.

Contact events: hand controls → graph plant run → actual Lean examples → exact
edge-cut comparison. No control or support implementation was changed after
the actual outputs were seen. Only the diagnostic wording parser was corrected.
These cases are now used evidence; they must not be described as fresh held-out
evidence for a later modified candidate.

## Verdict and limits

No counterexample to executable connectivity occurred in these 12 controls.
The independent graph argument gives a mathematical explanation for why the
read recursion extracts a connected support whenever a selected leaf occurs.
All 12 support equalities were checked by Lean's kernel, and all three planted
false equalities were rejected for actual falsity.

The final candidate proof, `ConnectedSupport`, `toRootedRegion`, and the deepest
root consumer were deliberately not inspected. Only the `Adj` and `Walk`
declarations were read to establish the graph correspondence above. The remaining
declaration and composition audit belongs to the other review arm. This report cannot award
VERIFIED-CLOSED to that full interface. Leastness formalization, unique-label
interpretation, and restriction transport remain outside its scope. The exact
arithmetic needs no precision ladder; no fitted constants or tolerances occur.
The general workspace validation suite was not run because no toolkit or
existing executable source changed. Only the stated focused checks ran.

## Report checks

The acceptance check uses exact finite sets, kernel-checked membership
equalities, independently authored controls, and failed corruption controls.
No fit or floating-point scientific quantity occurs, so decimal precision and
leave-one-out conditions do not apply. Timers measure wall time only. Two prose
passes checked scope, counts, source quotations, and the separation between the
ordinary mathematical derivation and the finite Lean examples. No assertion
of formal universal connectivity or complete consumer composition was added.
