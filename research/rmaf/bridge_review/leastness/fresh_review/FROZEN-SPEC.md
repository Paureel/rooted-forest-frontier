# Independent frozen controls and prefix/LCA derivation

Frozen before opening any candidate source or previous checker on 2026-10-14. Source of the target: `../../LEASTNESS-TARGET.md`. Author: fresh_review; no candidate code authored. Exact arithmetic throughout, no tolerances. Empty string denotes the input root; append 0/1 for left/right. These symbols will be mapped explicitly to Lean's orientation after source inspection.

## Specification
A rooted ordered full binary tree has one vertex for each actual subtree occurrence. Valid addresses are root and left/right extensions that traverse actual branch nodes. Leaf occurrences carry labels; distinct addresses may carry the same label. Given a label list S, U is the set of leaf addresses whose label occurs in S. Repeating a selected label does not repeat or create occurrences. A label can select multiple actual occurrences in a repeated-label tree.

For U nonempty let m be its longest common prefix. H(U) consists exactly of prefixes p of some u in U with m a prefix of p. For U empty set H empty. The ambient graph has an edge precisely between a valid address and one of its valid one-bit extensions. Supports are compared extensionally by membership, not list order or multiplicity.

Independent derivation (ordinary mathematics, not a Lean proof): all prefixes of a valid address are valid. H contains each terminal. Every p in H connects to m by deleting final bits, remaining in H, so H is connected. Every connected ambient support containing two terminals contains their unique simple path: delete an internal path vertex and the two terminals fall in different components of the ambient tree. For |U|=1, H=U. Otherwise maximality of m puts terminals in both child branches of m. Every p in H therefore lies on a path between one terminal below p and one in the opposite branch of m (and m lies on any such cross-branch path). Thus every connected ambient support containing U includes H. This proves leastness independently of extractor code.

Expected extractor recursion to inspect later: when only one root child has selected occurrences, descend into that child and prefix its minimal hull addresses; do not retain the current root or its initial path. When both children have selected occurrences, retain root and all vertices of paths from each child root down to selected occurrences. At a selected leaf retain its address. Equality to the actual unchanged extractor remains a separate, source-dependent obligation.

## Frozen positive fixtures
| id | tree | selection | terminals | expected H |
|---|---|---|---|---|
| crossing | ((a,b),(c,d)) | a,c | 00,10 | empty,0,00,1,10 |
| singleton | ((a,b),(c,d)) | a | 00 | 00 |
| siblings | ((a,b),(c,d)) | a,b | 00,01 | 0,00,01 |
| empty | ((a,b),(c,d)) | empty | empty set | empty set |
| absent | ((a,b),(c,d)) | z | empty set | empty set |
| root_leaf | a | a | empty string | empty string |
| root_absent | a | z | empty set | empty set |
| duplicate_labels | (a,a) | a | 0,1 | empty,0,1 |
| duplicate_selection | ((a,b),(c,d)) | a,a | 00 | 00 |
| duplicate_both | (a,a) | a,a | 0,1 | empty,0,1 |
| deep_suppression | ((((a,b),c),d),e) | a,b | 0000,0001 | 000,0000,0001 |

Here `empty` inside a nonempty address list means the empty string/root; `empty set` means no addresses.

## Frozen corruption fixtures and true twins
Each detector receives the exact H as a passing twin first. For crossing, delete 0: ambient true, terminals true, connected false. For siblings, add root: ambient true, terminals true, connected true, least false, witness H. For siblings add 000: ambient false, terminals true, connected true under the raw prefix-edge relation, least false. For siblings delete terminal 01: ambient true, connected true, terminal inclusion false. For root_leaf delete root: nonempty false and terminal inclusion false. For duplicate_labels replace occurrences by a single 0: reject terminal inclusion; any label-to-unique-address claim without uniqueness must fail on this tree.

The exact comparator must reject a known mismatched support even when both supports are connected, and pass equality with its clean twin. Malformed proof must produce a syntax/name/elaboration diagnostic and receive diagnostic-only status, never credit as rejection of the false theorem. Separately false Lean claims must fail for the intended proposition (or be positively refuted), paired with valid theorem twins.

## Bounded audit and gate
Write a new one-shot Python instrument with no prior checker imports or reads. Route A: selected-leaf LCA prefix set. Route B: intersect every nonempty connected ambient support containing all terminals (enumerate subsets); compare exact sets. Frozen tree family: all ordered full binary shapes through 5 leaves, each labelled by all assignments from {a,b}, all four selection subsets plus duplicate selections [a,a], [a,b,a], and absent [z]. Pilot controls and shapes through 2 leaves before larger enumeration. If runtime threatens hours, reduce bound with explicit downgrade; never label finite enumeration universal.

Candidate acceptance additionally requires independent full rebuild of unchanged RMAF, GraphRegion, PureBridge, completed ExecutableConnectivity and final TreeAddresses, ExtractorLeastness, ActualEmbedding, then reviewer interface tests. Hash every compiled source and compare source snapshots. Actual MinimalEmbedding must fill graph, ambient, terminals, support, all ambient/terminal/nonempty/connected/inclusion/leastness fields; only nonempty actual selected-label occurrence may be a target-specific input. Inspect leaf occurrence, label functionality, Instance uniqueness and original consumer application. No new axioms, sorry, admit, native_decide, unresolved triple-family imports, or implicit cross-tree transport. Standard axioms must be printed. Main report must scope claims to this source tree and compiled interface.

## Tool and independence ledger
Consulted `bootloops/tools/README.md`: no listed generic package provides binary-address finite graph least-support enumeration. Existing project checkers are deliberately not inspected because this task requires fresh code. A one-shot exact checker beside this review is warranted; it will not be registered as a reusable toolkit tool. Python runtime is `./bootloops-python`; compiler is `./bootloops-lean`. Deepest shared layers with the proof are the target's binary-tree/address specification, Python integer/set primitives, Lean kernel and the unchanged executable source. LCA semantics and brute-force graph-support intersection share parsed tree fixtures; corruption controls test that common parsing layer against hand-written expected addresses. Compilation confirms the proof source under its imports, not an independent proof of kernel consistency.
