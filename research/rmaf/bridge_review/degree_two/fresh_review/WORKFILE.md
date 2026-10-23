# Fresh nonauthor degree-two review

Status: target read; independent controls not yet run.
Scope: exact degree-two fixtures, scoped graph and partition consumers, pending final transport release. No G3/G4 closure is assumed.
Ownership: this directory only. No proof construction, no subagents, no aggregate counts.

## Target and frozen controls
Pending literal fixture freeze and checker interface before reading degree-two implementations.

## Independent checker
Pending independent exact tree/graph/partition implementation; no imports or code reuse from current checker.

## Controls and provenance
Pending positive controls, required deliberate mutations, joint-mark optima, source/log pins, semantic false Lean controls and positive twins.

## Scoped source audit
Pending graph propagation, partition refinement, consumer controls, local split/counting and controls; restriction route excluded pending release.

## Actual consumer hypotheses
Pending audit of original agreement and PureBridge.clearRest use sites; one-tree local split does not establish G3/G4.

## Verdict
Pending initial independent results and final release from parent.

2026-10-14: Read target first, wrote skeleton immediately. Read toolkit index and Gatekeeper guide; Gatekeeper is for oracle/fit integrity and does not implement finite tree-support graphs. A one-shot stdlib exact checker is justified by the required independent implementation; existing project checker and degree-two sources remain unread. Read required skills. An initial attempted pure_bridge path under bridge_review did not exist; resolved by filename inventory to research/rmaf/pure_bridge/VERIFY_SPEC.json. Its joint-mark literal costs are 1,1,1,2. FROZEN_CONTROLS.json now records expected values, mutation failures, checker interface and bounded pilot before implementation.

## Initial independent result
First exact checker run passed, with no debug edits. Verbatim retained stdout:
`{"status": "PASS", "controls": 42, "mutations": 6, "adversary": {"tree_count": 3, "considered": 171, "in_regime": 48, "fires": [], "elapsed_seconds": 0.0069143330001679715}, "elapsed_seconds": 0.00896933400144917}`
This is bounded evidence only. No inference of a universal theorem or G3/G4 closure. Shared layer with formal work: target/spec mathematical definitions and fixture literals; independent implementation uses BFS on actual parent/child graph and canonical suppressed shapes, stdlib only, no project code imports. Existing implementation/checker not read before this run. Precision is exact finite integer/set equality; precision doubling and fit hold-outs do not apply. All six predeclared false statements were rejected through the corresponding clean predicates/comparators. Source hashes are in pilot_results.json. Parent received initial results before source audit.

## Scoped source reading, initial pass
READ: DegreePropagation.lean lines 165–171 establishes `actual_degree_propagation` from label containment, actual B-support membership, nonterminal condition, and `ExactTwo` on S support. `ExactTwo` (15–17) enumerates exactly two distinct actual adjacent support vertices. The proof uses leastness through a connected support with a removable nonterminal leaf (71–117), rather than assuming the desired split.
READ: PartitionRefinement.lean 121–129 retains `RMAF.agreement` and requires nonempty blocks, label permutation, both subblock agreements, support containment separately in t/u, and disjointness separately in t/u. The consumer 233–250 also requires old per-tree marks and avoidance of v by both new t supports. Exact component growth is one (146–149), while forest-cut cost has only a bound without a lower bound on original piece count (224–229). Marks use distinct `mt` and `mu`; addresses are never identified between trees. These conditional consumers do not manufacture cross-tree transport.
READ: LocalSplit.lean 199–217 constructs existential blocks using a child of v, with hypotheses `(leaves t).Nodup`, `B.Nodup`, actual support membership and semantic degree two. Output gives nonempty disjoint label blocks, exact permutation, per-t containment, disjoint t supports, and t avoidance. It has no u variable. The split is computed by actual leaf occurrences below an actual child address (10–17), preserving unsuppressed support. DegreeCounting.lean 78–93 defines zero outside support, deduplicates neighbors (33–41), and proves count=2 iff actual membership plus `ExactTwo`; propagation at 95–101 carries the required nonterminal hypothesis explicitly. These sources close one-tree construction and numeric degree interpretation, but not the cross-tree obligations `ha0`, `ha1`, `hdu` of the consumer.
READ: ConsumerControls.lean 20–31 applies the actual conditional consumer to frozen quartet (three to four pieces); 51–62 retains nonempty old marks separately in both tree parameters. LocalSplitControls.lean 9–22 checks exact numeric degrees and unsuppressed support; 24–40 invokes the universal one-tree result on root/path positive twins. AgreementBlock.lean 22–30 derives B nonempty/Nodup, label inclusion in both input trees and original restriction agreement directly from the unchanged executable agreement predicate; it does not derive uniqueness of all input leaf labels.
READ: RMAF.lean 84–159 separates suppressed restriction shape from unsuppressed minimalVertices; `restrictionAgrees` rejects missing restrictions. `agreement` checks both partitions, blockwise shape agreement and pairwise support disjointness in each tree. It does not itself impose full-tree Nodup; input uniqueness comes from the target or Instance (19–24), and AgreementBlock only derives block-level properties.
READ: completed GraphRegion MinimalEmbedding (145–155) has original ambient, terminal, connected-support, inclusion, and leastness fields, with no split/transport conclusion installed. ActualEmbedding.embedding (9–23) derives those fields from actual extractor/occurrences. Its `embedding_support_exact` (33–36) keeps the full actual support. The graph propagation route imports this completed chain; the direct parent-prefix graph's `Adj` and unsuppressed support remain the semantics under test.
READ: PureBridge.ExchangeSystem.clearRest (79–80) is `∀ r, restValid r → ∃ r', restValid r' ∧ restAvoids r' ∧ restCost r' ≤ restCost r + 1`; paid_replacement uses it at 115. The arbitrary rest-valid predicate includes all existing marks/interactions (FORMAL.md paragraph 11). G3/G4 require local agreement transport and global forest realization; proving a local one-tree split alone cannot instantiate that field.
