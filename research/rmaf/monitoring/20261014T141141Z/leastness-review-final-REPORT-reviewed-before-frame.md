# Exact minimal embedding from the unchanged extractor

`LeastEmbedding.embedding` constructs `BridgeReview.MinimalEmbedding` from an
actual `RMAF.Tree t`, a selection `S`, and witnesses `x ∈ leaves t` and `x ∈ S`.
Its support list is exactly `RMAF.minimalVertices S t`. Its ambient and terminal
lists have proved interpretations as actual vertex addresses and selected leaf
occurrences. Ambient inclusion, terminal preservation and leastness are proved;
none is a constructor argument. The author audit kernel-checks this interface.
The independent semantic verdict is recorded separately in `acceptance.json`
and the fresh review receipts.

The unchanged source is `research/rmaf/lean/RMAF.lean`, SHA256
`4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`.
The result is about this ordered binary tree and address model. It does not
supply cross-tree restriction/suppression transport, G2–G7, the full exchange
construction, a safe-cover theorem, an unrestricted runtime bound or novelty.

## Mathematical statement and construction

An address is a finite Boolean list, with false for a left child and true for
a right child. `ValidVertex t v` is the inductive root/child occurrence relation.
`LeafOccurrence t v x` is the inductive leaf relation, retaining both address
and label. `TreeAddresses.lean` proves

- membership in `vertices t` is equivalent to `ValidVertex t v`;
- membership in `terminals S t` is equivalent to an actual leaf occurrence at
  that address with a label in S;
- a label belongs to `leaves t` exactly when it has a leaf occurrence;
- two leaf occurrences at the same address have the same label; each label
  occurring in `leaves t` has exactly one address when `leaves t` has no
  repeated labels;
- each permutation field of `RMAF.Instance` supplies this uniqueness for
  every label below `Instance.n`, and excludes other labels.

Arbitrary repeated-label trees are included in the constructor theorem. Selecting
such a label selects every occurrence. Repeated entries in the selection do not
repeat terminal addresses. `vertices_nodup` and `terminals_nodup` are proved for
all trees and selections. Empty or entirely absent selections have empty output
and do not satisfy the constructor's explicit occurring-selected-label premise.
A selected singleton-root leaf is included.

`ExtractorLeastness.lean` proves by structural recursion that every rooted-span
vertex has a selected terminal descendant, all selected terminals survive
`minimalVertices`, and every emitted vertex is an actual vertex. It also proves
that any common prefix of all selected terminals is a prefix of every emitted
minimal vertex. In the two occupied child branches this common prefix is empty;
in a single occupied branch the recursive argument retains that child's address
prefix. No unproved equality with a separately defined hull is imported.

For a competing `ConnectedSupport`, its already proved graph-to-region map gives
a root above all its vertices and convexity along ancestor paths. Its root is
therefore a common ancestor of the selected terminals. Given an emitted vertex
v, choose a selected terminal below v. The common-ancestor lemma places the
competitor's root above v; its convexity places v in the competitor. This is
`minimal_least`. It holds for every connected competitor containing the selected
terminals, even without requiring that competitor to stay in the input ambient
tree. It therefore supplies the narrower ambient-bounded `minimal` field.

The constructor uses the previously audited `extractedSupport` for connectivity
and exact support-list preservation. `embedding_region_exact` identifies the
existing `MinimalEmbedding.region` membership with the unchanged extractor.
`embedding_consumer` calls the original
`MinimalEmbedding.deepest_root_in_neighbor`, retaining its depth and overlap
hypotheses, and returns exact extractor membership. Equality of coordinates from
different input trees is only equality of address lists; this theorem does not
establish a correspondence between those trees.

## Executed evidence and provenance

The isolated author build in `audit/certificate.json` rebuilt RMAF, PureBridge,
GraphRegion, ExecutableConnectivity, TreeAddresses, ExtractorLeastness,
ActualEmbedding and LeastnessControls into a new import directory. It checked
66 named new theorems: 22 semantic, 13 extractor, 7 constructor/interface and
24 control theorems. The generated inventory prints axioms for those theorems
and 9 definitions: all 75 reports use only the standard permitted axioms
`propext`, `Classical.choice` and `Quot.sound`, or none. Production sources
contain no custom axiom, `sorry`, `admit`, `native_decide` or unsafe declaration.
Imported old declarations and independent finite-panel equalities are outside
this scoped count. The parent maintains the project aggregate.

The nine frozen fixtures cover crossing quartet leaves, a singleton, siblings,
empty and absent selection, a singleton-root tree, repeated labels, repeated
selection and a deep omitted initial root path. Their 18 exact terminal/support
values compile. Six additional theorems include the critical distinction: an
added input root leaves the sibling support connected but violates leastness.
They also prove failure of path deletion, invalid ambient address and missing
selected terminal. Five separate false assertions are rejected by Lean's
explicit `decide` falsity diagnostic. A true proposition with an ill-typed proof
is rejected as a malformed control, and is not counted as a false proposition;
its correctly typed twin compiles. Six planted diagnostic-parser cases pass.

The pre-construction adversary used edge deletion and exhaustive connected
ambient subsets, with fresh code and no candidate leastness proof access. Its
bounded corpus has 816 cases and 85,488 ambient subsets; 826 finite source
equalities (including ten hand fixtures) compile. Five corruptions and clean
twins pass, two false assertions fail semantically, and a malformed proof is
separately rejected. Its ordinary edge-separation derivation is not advertised
as an additional universal Lean proof. These finite checks cannot prove the
unbounded claim. Full records are in `adversary/`.

The main author had prior source knowledge from the completed connectivity
checkpoint. Its controls were frozen before new leastness proof construction,
not before all source contact. The semantic module author is a coauthor, not an
independent verifier. The fresh reviewer starts from the target, freezes a
prefix/LCA derivation and exact controls, and writes a new graph-support
intersection enumerator before inspecting the candidate. All arms share the
formal statement, Lean kernel and original RMAF source. The author audit driver
and parser derive from the preceding executable audit and are not an independent
mathematical reference. These dependencies are explicit in `INDEPENDENCE.json`.

Failed development attempts are retained. The first general proof attempt had
Lean API elaboration errors. The first fixture generator omitted parentheses
around leaf constructors. Repairing that syntax changed no frozen expected
value. Those failures do not count as negative mathematical controls.

## Scope of acceptance

The new result fills the ambient interpretation, selected-occurrence and
leastness fields missing from the earlier exact executable connectivity
checkpoint. Its original consumer call is kernel-checked. The broader bridge
route still needs transport between restricted or suppressed source and target
trees, degree-two split realization, marked-interaction and exchange interfaces,
and the safe-cover/Whidden `2^q` audit. No running-time or novelty conclusion
follows from these local support theorems.

The exact audit command is
`./bootloops-python research/rmaf/bridge_review/leastness/audit.py`.
The project-wide `bootloops-check` suite was not run: this checkpoint changes
only new Lean proof and audit files and uses a complete isolated rebuild of its
actual dependency chain. No unavailable engine is needed for this checkpoint.
