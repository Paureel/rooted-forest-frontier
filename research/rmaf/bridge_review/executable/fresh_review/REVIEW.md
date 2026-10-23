# Fresh executable semantic review

Status: target read; skeleton created before candidate source inspection.

## Target interpretation (frozen before candidate inspection)

For each frozen executable tree t and selected set S, the exact vertex predicate `RMAF.minimalVertices S t` must be connected under `BridgeReview.Adj` and `Walk` whenever nonempty. The constructed `ConnectedSupport` must preserve this predicate exactly. Nonemptiness must follow from an actual selected leaf of t. The proof may use the frozen extractor definitions and audited graph results, but cannot assume extractor connectivity, convexity, ancestry or correctness. The original deepest-root consumer must accept the constructed rooted region.

This review will not claim leastness, uniqueness of labels, restriction transport, global G1 completeness, or algorithmic bounds.

## Independent hand controls (frozen before candidate inspection)

Path convention: false = left, true = right. For t=((0,1),(2,3)):

- Empty S: empty support.
- Absent S={9}: empty support.
- Singleton S={1}: {[false,true]}.
- Branching root S={0,2}: {[],[false],[false,false],[true],[true,false]}.
- Initial suppressed path S={0,1}: {[false],[false,false],[false,true]}.
- Malformed branching support deleting [false] must fail connectivity: [false,false] is isolated from the remaining selected leaves/root.
- Positive twin restoring [false] must pass.

Further source-sensitive controls to freeze from mathematical interpretation now:

- t=leaf 7, S={7}: {[]}.
- t=leaf 7, S={8}: empty support.
- t=((0,0),(2,3)), S={0}: {[false],[false,false],[false,true]} if selection is by label occurrence. A singleton label is not necessarily a singleton vertex when labels repeat.
- t=(((0,1),2),3), S={0,1}: {[false,false],[false,false,false],[false,false,true]}, suppressing two initial edges.

Any disagreement with these expectations must be recorded before changing them.

## Inspection and evidence

Pending.

### Source read 1: frozen executable definitions

Read `research/rmaf/lean/RMAF.lean` in full with line numbers. Lines 109–133 define vertices as Boolean paths, `rootedSpan` as root-to-selected-occurrence support, and `minimalVertices` by descending through a sole contributing child and retaining `rootedSpan` after the first branching selection. Load-bearing exact source: `if ls.isEmpty then prependSide true (minimalVertices selected r)` (line 131); `else if rs.isEmpty then prependSide false (minimalVertices selected l)` (132); `else [] :: (prependSide false ls ++ prependSide true rs)` (133). This matches the frozen hand interpretations, including repeated labels. The type `Tree` (8–11) itself imposes no label uniqueness; uniqueness is in a separate `Instance` (19–24). No semantic discrepancy found at this read.

### Tool choice and lineage freeze

Consulted `bootloops/tools/README.md`, `bootloops/toolkit/ours/README.md`, and `bootloops/toolkit/external/TOOLS.md` by formal-proof/graph/exact capability. No general toolkit package covers this one-off Lean executable-interface review; the existing `bootloops-lean` wrapper and the pinned Lean runtime cover kernel elaboration. A small one-shot orchestration script and independent finite path-hull controls are justified for retained receipts and hostile instances. No existing project Python oracle/checker will be read or imported. The source definitions, mathematical rooted-tree/path model, Lean kernel, and Std are necessarily shared; the reviewer controls and graph traversal will be fresh code. This does not constitute independent mathematics or an independently implemented kernel.

Timing policy: runtime initially unknown; measure the wrapper's minimal known-answer elaboration first, then record each fresh dependency build separately with bounded timeouts. Scientific progress units are successful exact statements and observed deliberate failures, not exit status alone.

### Source read 2: candidate exact connectivity interface

Read `executable/lean/ExecutableConnectivity.lean` in full. `Connected` (10–11) is exactly pairwise `Walk` in list membership. `minimalVertices_connected` (109–127) quantifies over arbitrary selections and trees and assumes no connectivity hypothesis. Its construction follows the extractor's three branches, using only prefixed induction for a single child and `rootedSpan_connected` at a branching root. `extractedSupport` (170–177) needs only nonempty output; exact list equality appears at 179–182, exact rooted-region membership at 188–192. The consumer theorem (196–204) retains only nonemptiness, the printed root-depth comparison, and an actual shared vertex. These are source-level observations; independent elaboration and graph-definition audit remain pending.

### Source read 3: supplied controls

Read `executable/lean/ExtractorControls.lean` in full. Lines 11–16 state the five target outputs and rejected deleted-path list by kernel `decide`. Lines 18–23 prove the deleted support has no root-to-[false,false] walk, via the graph ancestor-between theorem. These are candidate controls, hence not the independent hand fixtures or fresh reviewer checker; both sides will be elaborated separately in the review build.

### Source read 4: graph dependency

Read `bridge_review/lean/GraphRegion.lean` in full. `Adj` (9–10) is exactly append-one-bit parent/child adjacency. `Walk` (12–14) keeps both initial and newly visited vertices inside the predicate. `ConnectedSupport` (87–91) contains connectivity, but the executable adapter constructs that field from its proved theorem; it does not pass it as an assumption. `toRootedRegion` (106–112) derives ancestry and convexity from finite walks and a minimum-depth root. `deepest_graph_root_in_neighbor` (123–127) calls `PureBridge.deepest_root_in_neighbor` directly. The `MinimalEmbedding` wrapper (145–155) contains extra leastness/ambient/terminal assumptions but does not occur in the executable proof chain (imports alone do not instantiate these hypotheses).

### Source read 5: original consumer

Read `pure_bridge/lean/PureBridge.lean` in full. The original `RootedRegion` (14–19) needs root membership, descendants below that root, and ancestor-path convexity. The original consumer (23–31) needs exactly a root-depth inequality and an intersecting vertex. GraphRegion supplies the region fields from walks, while the executable candidate supplies those walks from the actual extractor. There is no missing or extra geometric hypothesis in this use-site. This source trace supports only the requested deepest-root consumer, not every theorem in PureBridge or a full graph-semantic algorithm interface.

### Fresh checks registered before execution

The independent finite route enumerates leaf addresses directly, selects all occurrences of selected labels, computes their common prefix, and takes the union of prefix segments from that prefix to the selected leaves. A separate parent/child BFS checks induced-support connectivity. This avoids reimplementing the extractor's recursive `rootedSpan`/`minimalVertices` branches. It shares the intended path-hull mathematics with the task and therefore cannot independently establish that those semantics are the scientific model intended outside this target.

The exact finite panel is all full binary ordered shapes with 1–4 leaves, every 0/1 labelling, and all eight subsets of {0,1,9}: 816 tree/selection cases. It includes duplicate labels, absent labels, empty selections and deep suppression. Frozen controls above are checked first. Every expected support is encoded in a fresh Lean `by decide` equality to the actual source extractor; BFS checks connectivity and selected-leaf preservation independently. False list equality and malformed-name controls must both exit nonzero, but only the expected kernel `decide` false-proposition diagnostic may count as a successful false-proof rejection. A clean twin must elaborate.

### First execution and retained harness failure

`logs/pilot.json`: trivial Lean known-answer elaboration passed in 0.330 s. The independent hand controls passed before source builds. `logs/run-01.log` records fresh builds (RMAF 5.382 s, PureBridge 0.442 s, GraphRegion 0.371 s, candidate 0.334 s, supplied controls 0.305 s). Fresh exact controls: 9 hand cases + 816 finite cases compiled in 1.917 s. Positive twin compiled; false and malformed controls both failed.

The first review driver exited at its own expected-diagnostic assertion: it expected lowercase `tactic 'decide'`, while the retained real compiler output uses capitalized/backtick `Tactic `decide``. This was a fail-closed parser mismatch, not a candidate proof or frozen-value discrepancy. The original run and compiler failures remain retained. The parser was corrected to match the actual documented evidence, additionally require the precise planted false equality, exactly one error, and no unknown-name error. Revalidation is recorded separately; no candidate/source/fixture changed.

`logs/interface-audit.log`: independent exact-Walk restatement, selected-occurrence region constructor, exact membership theorem, and direct original-consumer composition all elaborated in 0.435 s. Their printed dependencies are subsets of {propext, Classical.choice, Quot.sound}. The signature audit confirms no hidden geometric premise.

### Executed axiom/source audit and semantic verdict

`logs/axiom-source-audit.json` records 81 printed declarations across the five rebuilt modules plus the fresh interface audit. Every printed dependency list is a subset of {propext, Classical.choice, Quot.sound}; the declaration-count check matched every `#print axioms` in those files. Code-token checks after comment removal found no `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` in these six modules. A planted axiom is rejected by both the source-token detector and axiom allowlist. This is a source/printed-dependency audit, not an independent Lean implementation.

`logs/SUMMARY.json` and `logs/parser-revalidation.json` record: 9/9 hand controls, 816/816 finite exact cases, 816/816 independent BFS checks, clean twin accepted, deliberate false equality rejected for its specific expected reason, malformed-name negative refused as evidence, and four hostile parser mutations rejected. The original five source SHA-256 hashes were identical before/after rebuilding. The finite panel is corroboration; the all-tree connectivity claim rests on the kernel-checked structural theorem.

Current ruling: CONFIRMED for exact executable connectivity, nonemptiness from a selected leaf occurrence, exact `ConnectedSupport`/`RootedRegion` membership, and composition with the original deepest-root consumer under its stated depth/overlap hypotheses. No additional connectedness, convexity or ancestry input is required. Leastness, unique-label interpretation, ambient realization/transport, source/target restriction transport, global G1 completeness, and algorithmic/runtime claims are outside this verdict. Repeated-label controls demonstrate that the connectivity theorem allows duplicate labels; they do not establish the unique-label semantic obligation for an rMAF instance.

### Independence ledger

Birth: hand expected values written in this file before candidate/source inspection, 2026-10-14. Fresh finite expectations were generated by this review's leaf-address/common-prefix/segment-union code, not by the extractor or an existing oracle. Exact integer/Boolean values have no numerical precision tolerance. Contact: hand/finite values checked only this frozen candidate; neither was used to change it. Reviewer authored no candidate theorem. Shared dependencies: frozen RMAF/GraphRegion/PureBridge source, Std, Lean kernel, path-address mathematics. Separate review code: hull construction, BFS, malformed-diagnostic checker, interface restatement. The fresh replay detects stale dependency artifacts and interface misstatements; it is not an independently derived formal connectivity proof.

### Final report semantic review

Pending parent report creation. No full graph-semantic closure grade is assigned here.

### Pinned report review completed

Reviewed `REPORT.md` snapshot SHA-256 `a72c4f53476558e1277d95de8dc3c79748d5bd6dc879f941e87ed87dc2430ca9`; retained as `REPORT-reviewed-01.md`. `referee_sim_REPORT.md` records five audiences with separate correctness/novelty objections. No mathematical overclaim found. One required precision edit replaces head/tail “concatenation” with `head :: tail`; one recommended sentence distinguishes equality of addresses across trees from unproved source/target transport. The opening correctly leaves leastness, label interpretation and transport open. The report's 24-theorem and 26-axiom-report counts agree with the freshly inspected source/build output.

Only after completing the independent proof/interface/finite checks, the author `audit/certificate.json` was opened to check the report's attribution of 8.005 seconds and five parser controls. These are retrieved author-receipt facts, not independent-review measurements; no author audit code or existing Python oracle was used for the review's conclusions. `report-review.json` preserves this distinction. Full visual typesetting review is not claimed for this plain Markdown semantic review.

### Complete reproducible replay after parser repair

The one-shot `run_review.py` now retains every replay in a timestamped log directory, includes the direct consumer audit and the complete 81-declaration axiom audit, and tests five hostile parser mutations. Running it with `./bootloops-python research/rmaf/bridge_review/executable/fresh_review/run_review.py` completed successfully; see `logs/run-02.log` and `logs/replay-20261014T133015425804Z/SUMMARY.json`. The original failed run remains untouched. Fresh controls elaborated in 1.719 s; direct interface audit in 0.314 s; dependency/module builds and expected false failures each have their own measured duration in the replay receipt. All five original source hashes still match. The summary records 9 hand controls, 816 finite exact cases, 816 BFS cases, the positive/deleted/malformed controls, five parser mutations, and 81 standard-only axiom reports. `InterfaceAudit.lean` is retained as a reviewer-owned source beside this journal, so the complete review can be rerun from one command.

### Final report/receipt check

The final report is pinned as `REPORT-reviewed-final.md`, SHA-256 `33479a00ddb6081588a53e642f033404937a58c7ecf4deb7661079ed4a7f0acb`; details and receipt hashes are in `report-review-final.json`. The final diff and full report were reread. The prefix route's nine hand controls, four rejections, 816 finite comparisons and generic prefix-hull theorem agree with its opened receipt, result JSON, generated declaration counts and proof statements. Its general executable/hull equality remains unformalized, and the report says so explicitly. The edge-cut route's 12 exact support matches and three semantic false controls agree with its opened receipt, JSON and actual diagnostic logs. Its general correspondence is explicitly ordinary written mathematics. The report preserves shared prefix-hull mathematics, shared source/address/Lean layers, and overlapping finite panels without summing them as unique coverage.

All five proof source hashes still match the fresh rebuild. No proof work or broad rerun was performed for this final receipt check. The final scientific scope remains exact executable connectivity, selected-occurrence nonemptiness, exact membership and original consumer composition. No remaining semantic or prose-integrity corrections were found for the pinned final report. Stronger obligations remain open as stated in the report.
