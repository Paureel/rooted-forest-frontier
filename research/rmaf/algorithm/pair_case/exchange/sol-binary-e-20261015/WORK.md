# Binary E source/target exchange workfile

Status: OPEN; author construction only; no universal exchange or algorithm claim.
Scope: TARGET-v1.md E only, original distinct-label rooted binary S,T, proper P, mutually clear four sectors, A rooted agreement. No whole-B agreement assumed.

## Frozen target
Target read before supporting sources: research/rmaf/algorithm/pair_case/TARGET-v1.md.

## Proof obligations
1. Read actual agreement, partition, refinement and minimal embedding definitions.
2. Prove at most one F block in B crosses the target edge.
3. Transfer target descendant cluster of that agreed B block to its source restriction.
4. Restrict/split that block into source-disjoint agreed blocks using one source edge.
5. Merge all F blocks of A, preserving source and target disjointness.
6. Preserve outside blocks and refinement; prove block-count inequality.
7. Retain source-bound Lean replay and axiom audit, positive and genuine false controls.

## Evidence ledger
Pending.

## First missing formal step
Definitions and reusable formal interface not yet inspected.

## Consumer limitation
A partition exchange alone leaves original residual source-cost reconstruction and the complete faster algorithm OPEN.

### Protocol setup
Read project AGENTS.md, toolkit roster, and prove-protocol. No general toolkit package directly supplies rooted-AF graph surgery; Lean is the proof route. This is the fixed-target regime. X0 execution is supplied by the parent; fresh semantic/consumer review is outstanding. No children are spawned in this assigned phase. Frozen scripts/results will not be edited.
Reading-contract applied: source claims will carry file/declaration locators; derived claims will be labeled derived. No literature novelty claim is attempted.
Tool-stewardship applied: toolkit capability roster has no original-address RMAF exchange prover; original project Lean definitions and checked reusable lemmas will be extended only in this arm's directory. Any new audit/replay script is one-shot source-bound evidence, not a promoted general instrument.
Planted-truth applied: literal finite graph controls already ran in separate X0 before construction; their pin/receipts are permitted evidence. For any fresh formal audit, freeze positive, false-declaration, and compilable-custom-axiom controls before the audit. Do not treat compiler failure alone as semantic falsity.
Timing-discipline applied: initial Lean import/compile is the measured pilot; no broad census or overnight computation planned. Progress unit is a compiled theorem with retained replay/audit receipt, not CPU or exit status alone.
Independence-bookkeeping applied: X0 is a separately authored preconstruction finite hunt; its receipts are retrieved evidence, not a proof. This author can deliver kernel-checked theorems and self-checks only. External semantic/interface review remains required, and no unfinished G/core/profile argument will be read.
Acceptance-gate applied: finite control success is not universal closure; author Lean grade requires retained kernel proof and full originating-module axiom audit. Overall E acceptance remains pending nonauthor semantic/consumer review.

### Actual definitions read
Source: research/rmaf/lean/RMAF.lean, declarations `Tree`, `RootedIso`, `restrict`, `rootedSpan`, `minimalVertices`, `partitionCheck`, `agreement`.
Read: trees are full binary syntax with Nat leaf labels. Restrictions suppress unary vertices and return `Option Tree`. Actual unsuppressed embedding addresses are `List Bool`; `minimalVertices` starts at the selected LCA and retains unary span paths once both children contribute. `agreement` is the conjunction of both actual partition checks, all restriction checks, and source/target pairwise embedding checks. `Instance` enforces distinct labels through `Perm (List.range n)`, but E may use a direct distinct-label hypothesis rather than the canonical range.
Read boundary: the original finite assignment solver explicitly separates executable-model optimality from graph-theoretic paper semantics. No exchange theorem occurs in this source.
Geometry README read: imports may be sourced from Geometry/Bridge/Composition, but its author replay alone is not independent review. Parent licenses the independently reviewed frozen geometry only at exact hypotheses. No source/core exchange conclusion will be imported from this package.
Geometry RESULT read (retrieval): exact bridge `minimalVertices_correct` holds for every selection/tree/address. `Hull` is path-between-selected-leaves. Proper labeling is needed only at original-label address/color transport. This E arm will use the bridge and convexity if needed, not conditional core realization or faster-runtime claims. The result's printed absence of source history/realization theorems is retained as scope, not repaired by assumption.
Geometry.lean read: reusable actual path facts include `path_region_ne`, `region_ne_path`, `avoids_iff_monochromatic` with essential nonlabel hypothesis, `region_path_closed`, `hull_convex`. Definitions are on original `List Bool` vertices, with singleton hulls retained. No rooted restriction or cluster-transfer theorem occurs there.
Bridge.lean read: actual Boolean pairwise embedding check is equivalent to pairwise disjoint `Hull selectedLeaves`; `selected_leaves_mono` permits embedding monotonicity by label subset. `selected_decompose_label` and distinct-label singleton address uniqueness are available. `Bridge` contains no restriction shape or cluster transfer facts. These imports remain exact source dependencies.
Parent supplied exact checked-source locator ProductTopology.lean for restrictionAgrees_join; no general restriction-composition/cluster-transfer theorem located. No specialized family theorem is imported as a general seam. Pilot: original RMAF source compiled locally with Lean 4.35.0 in about six seconds; exact `/usr/bin/time` output retained in build/pilot-rmaf.log.

### Formal checkpoint 1
Restriction.lean compiles against fresh unchanged RMAF source (restriction-03.log). Derived universal statements: label membership under restriction, restriction composition via filter, subset restriction idempotence, rooted-isomorphism restriction transport, and agreement of every nonempty subblock whose labels occur in source. This is only the restriction foundation; E remains OPEN. Full declaration audit not yet executed.

### Formal checkpoint 2
Cluster.lean compiles (cluster-02.log). Derived `agreed_cluster_split`: if target true-colored C leaves are empty or one rooted cluster, and ONLY C's S/T restrictions agree, then source has that cluster too and true/false C sectors have disjoint actual original source and target minimal embeddings. The intermediate `Cluster` is constructed recursively and its transfer is proved through restriction + RootedIso, not an exchange field. `cluster_disjoint_span` proves a stronger original rooted-span separation, covering unary paths. The remaining first gap is deriving this target cluster from the literal original target edge, then assembling the full actual agreement partition and count.

### Formal checkpoint 3
Descendant.lean compiles (descendant-02.log). `treeAt` names literal original subtrees. `subtree_cluster` uses distinct input labels to prevent repeated descendant labels outside the subtree. `selected_descendant_iff` binds label membership to original-address prefix through singleton uniqueness. `crossing_occupies` includes root/singleton boundaries naturally: an actual mixed C occupies the child endpoint. `descendant_agreed_split` now supplies the required target-edge-to-source-separation bridge, with no whole-B agreement premise.

### Formal checkpoint 4
Forest.lean and Surgery.lean compile (forest-03.log, surgery-02.log). `exchange_valid` constructs literal `A :: (splitAll V q ++ W)` and proves `RMAF.agreement=true` from an actual agreed displayed decomposition U++V++W, partitionCheck A U, original source A/B disjointness, original target A/B-sector clearance, and source/target A/W clearance. `splitAll` preserves every label count; each split sector remains a restriction agreement and actual minimal embeddings are pairwise disjoint. No component-count theorem is included in this checkpoint yet.

### Formal checkpoint 5
Count.lean compiles (count-02.log). `mixed_blocks_at_most_one` proves the target child endpoint can belong to at most one mixed final B block. `exchange_size` proves the actual displayed output has at most the old block count: when a crossing B block exists, target disjointness forces the two A-sector labels into distinct old A blocks; merging pays the single extra split. This uses actual AF ownership, not an assumed count field. Remaining seam: extract/display U,V,W from arbitrary actual F refining proper P and transport agreement through their permutation.

### Formal checkpoint 6
Parents.lean compiles (parents-02.log). Derived extraction from arbitrary F refining proper P: `aParts`, `bParts`, `outside` form an executable list permutation of F; `apart_partition` proves partitionCheck A aParts; nonempty disjoint parent labels have a unique refinement owner. `agreement_perm` transports the actual executable AF checks through the displayed permutation. This closes the displayed-decomposition seam; final exported theorem and preservation interfaces are being assembled next.

### Formal checkpoint 7
Exchange.lean compiles (exchange-02.log). Exported universal theorem `BinaryExchange.binary_exchange` constructs `exchange A B F u`; its conclusion is actual agreement, refinement of P, exactly one A block, monochromatic B blocks relative to original descendant labels, nonincreasing component count, and literal equality of the outside-block filters. Hypotheses retain original distinct labels, equal input leaf sets, proper source P with disjoint original source embeddings, A/B distinct parents, nonroot literal target child path, four nonempty sectors, bilateral actual sector clearance, other-parent target clearance, and A-only restriction agreement. Some retained premises are mathematically stronger than this surgery needs; no conclusion is hidden in a structure field.
This is author kernel construction pending comprehensive axiom audit, controls, fresh replay and nonauthor semantic/interface review. Original source-cost/reconstruction interface remains OPEN.

First fresh replay 20261015T083007Z preserved with FAILED manifest: all 12 scientific modules compiled; audit enumerated 826 originating declarations with zero forbidden dependencies, but audit compilation failed because a doc comment cannot attach to `run_cmd`. That failed run is not an accepted audit. Repaired the audit comment to an ordinary block comment and rerun from fresh source/olean snapshot.

Erratum to first replay journal count: the exact inventory sum is 726, not 826. Accepted first complete fresh replay is results/algorithm-pair-case-exchange-20261015T083049Z: 726 declarations, 22 run receipts, five semantic false catches, clean axiom twin, compilable custom-axiom+private-theorem rejection. The failed 083007Z replay is retained.

### Stronger source-edge checkpoint and T1
SourceEdge.lean compiles (source-edge-02.log): `descendant_final_source_edge` constructs a proper nonroot ORIGINAL source subtree address whose descendant labels agree exactly with the target descendant color ON A MIXED AGREED FINAL C. This statement never claims the whole original B can clear in one cut. Full residual source-forest cut/reconstruction cost interface remains OPEN.
T1.lean compiles in the measured one-second-scale local run (t1-01.log): independent canonical enumerator yields 877 partitions, 30 refining P, 15 with A whole; both restricted minima are five by kernel `decide`. This is an independent implementation from X0, but not a universal completeness theorem for that finite enumerator. `T1_universal_consumer` explicitly instantiates every universal E hypothesis on the literal pinned seven-label pair. Additional six-label original-root overlap and surgery control is retained. Audit/replay is being rerun with these additional modules, and its custom-axiom condition now checks the precise private plant line and exact two forbidden declarations.

### Final author delivery
Final accepted source replay: results/algorithm-pair-case-exchange-20261015T083439Z, AUTHOR-LEAN pending fresh nonauthor semantic/consumer review; 14 scientific modules, 766 all-origin declarations, 24 retained run receipts. The result source manifest matched all 24 current source origins exactly. Target SHA-256: 6ed7fc1d0dd7b8fb1bd496754300e9821f6a1a08ef98c60fb23c46625693aa3e.

Universal E and the final-C literal source-edge witness have no remaining author formal proof hole. The first remaining acceptance step is the fresh nonauthor semantic/interface review. The first remaining algorithmic formal step is residual-source-state/cut-cost reconstruction connecting an exchanged final F' and its local final-C edge to the algorithm's actual emitted source operations. No faster algorithm is announced.

REPORT.md, AUTHOR-INTERFACE.md, and EVIDENCE.json give exact hypotheses, actual-AF correspondence, controls and source provenance. Prose-lint was applied in two author passes: numerical/scope claims were checked against manifest/declarations first; declaration-name errors in the draft were corrected; meaning and register were checked separately. referee_sim_REPORT.md is an explicit pending-review objection table. The fresh-context requirement cannot be self-certified, and no child agent was spawned in this phase.
