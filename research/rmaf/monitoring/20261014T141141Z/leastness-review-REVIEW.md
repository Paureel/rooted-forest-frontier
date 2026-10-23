# Fresh leastness and semantic review

**Assessment: confirmed for the pinned target and source snapshot.** The actual `LeastEmbedding.embedding` returns the original `BridgeReview.MinimalEmbedding` from a tree, a label selection and one label occurring in both. Its support list is exactly the unchanged `RMAF.minimalVertices`; its ambient list is exactly the actual vertex addresses; its terminals are exactly selected leaf occurrences. Ambient inclusion, terminal preservation and leastness are derived. I found no candidate proof defect or counterexample.

The result concerns the ordered binary-address model. It does not provide cross-tree restriction/suppression transport, G2–G7, the exchange construction, a safe cover, a faster runtime bound or novelty. The original consumer has explicit depth and coordinate-overlap hypotheses. Its successful use does not identify vertices between different input trees.

## Independent derivation and controls

I read `LEASTNESS-TARGET.md` first and froze `FROZEN-SPEC.md` before reading candidate sources or earlier checkers. Its SHA256 is `50482f86856d2904569e6e22d1be8061de83c265af90ad3da1543d9476035af8`. The independent derivation defines the selected occurrence set U, its longest common prefix m, and the hull consisting of all prefixes between m and a terminal. A connected ambient support containing U must contain every terminal-to-terminal path; every hull vertex lies on such a path when U has at least two occurrences. A singleton occurrence has a singleton hull. This is an ordinary derivation, separate from the universal Lean proof.

The one-shot Python instrument was written before candidate source inspection and shares no code with previous checkers. Its LCA-prefix construction was compared against the intersection of every connected ambient support containing the terminals. Through five leaves, 3,850 tree/selection cases contain 2,681 nonempty selected-occurrence cases and 1,169 empty/absent null cases. The nonempty cases enumerate 16,373 feasible connected supports. Empty cases use the explicitly frozen empty-output convention; they do not assert existence of a nonempty MinimalEmbedding with no terminals. All 17 literal fixture/corruption controls passed. The six corruptions have passing twins and include path deletion, an extra root, an invalid address, a missing terminal, empty singleton support and collapsed repeated-label occurrences. Full receipts: `lca-check-2.json`, `lca-check-4.json`, `lca-check-5.json`.

The frozen expectations were then compiled against the unchanged RMAF and final TreeAddresses definitions. All 3,850 generated finite theorems, each checking support and terminals, passed: 7,700 exact equalities and 3,850 empty axiom reports. Pilot panels through two and four leaves preceded the full run; the full source panel took 27.901143374998355 seconds. See `source-panel-5.json`, its log, and `build/FiniteSourcePanel5.lean`. Finite enumeration does not establish the unbounded claim.

## Exact semantic and constructor trace

All line references below refer to the source hashes in `source-manifest.json`, retained in `build/`.

| Obligation | Source and exact use | Assessment |
|---|---|---|
| Actual valid vertices | TreeAddresses 10–12, 20–23, 33–64: traversal membership iff inductive ValidVertex | Every address traverses actual children; the input root is valid. |
| Selected leaf occurrences | TreeAddresses 14–17, 26–31, 66–99: membership iff an occurrence at that address has a selected label | Repeated labels select all occurrences; repeated selection entries create none. |
| Label correspondence | TreeAddresses 108–138: leaves membership iff occurrence exists; label_unique at one address | Functionality applies to leaf occurrences, with no false total labelling of internal nodes. |
| Address uniqueness | TreeAddresses 153–174: address_unique and occurrence existence under leaves.Nodup | Duplicate-labelled trees are not given address uniqueness. |
| Instance uniqueness | TreeAddresses 176–206: each permutation to range gives Nodup and exactly labels below n | Left and right occurrence witnesses are separate; no equality of their addresses is inferred. |
| No duplicate listed addresses | TreeAddresses 208–249: vertices_nodup and terminals_nodup | Applies to repeated-label trees and repeated selections. |
| Support and connectivity | ExecutableConnectivity 151–182; ActualEmbedding 14 and 33–36 | Nonempty head/tail support retains the exact minimalVertices list and its proved graph walks. |
| Ambient field | ActualEmbedding 11, 15–17; ExtractorLeastness 77–126 | The actual traversal is used; emitted vertices are proved members. |
| Terminal field and nonemptiness | ActualEmbedding 12–13; TreeAddresses 145–150 | One selected occurring label supplies an actual selected occurrence. |
| Terminal inclusion | ActualEmbedding 18–20; ExtractorLeastness 129–149 | Structural proof handles initial-path suppression branches. |
| Leastness field | ActualEmbedding 21–23; ExtractorLeastness 176–220 | Every common terminal ancestor prefixes each emitted vertex; any connected competitor's region then contains that vertex. No target field is assumed. |
| Original record contract | GraphRegion 145–155 | All original fields are filled; leastness covers every ambient connected support containing terminals. The proved lemma is stronger because it does not need ambient inclusion. |
| Exact region | ActualEmbedding 47–52; GraphRegion 159–163 | The original region's member predicate is exact extractor membership. |
| Original consumer | ActualEmbedding 56–65; GraphRegion 165–170; PureBridge 23–31 | The original theorem is actually called with its depth/overlap assumptions; no bridge transport is supplied. |

`build/ReviewerChecks.lean` independently restates the constructor, consumes every field in `useAllFields`, and calls the unchanged consumer in `originalConsumer`. It compiles against the final source snapshot. It also proves that the extra-root support is connected, is ambient-valid and contains terminals, yet fails leastness; deleting an intervening path vertex breaks connectivity; an invalid address and missing terminal are rejected. Repeated-label injectivity is positively refuted, while leaf-label functionality and per-tree Instance uniqueness compile.

## Fresh build, provenance and diagnostics

All seven dependency modules were rebuilt into this review's directory with `./bootloops-lean` and LEAN_PATH restricted to `build/`. No earlier project olean was used. The final TreeAddresses hash is `f2bbd08201b98893a0e824f041e9af72761933d7f29b4e9a89088d9d9e46fdb0`. Current/snapshot parity holds for all seven sources. RMAF, PureBridge, GraphRegion and ExecutableConnectivity also match their retained completed-checkpoint sources. See `build-pilot.json`, `build-main.json`, `build-review.json`, `source-manifest.json`, and `source-audit.json`.

The whole-chain axiom inventory queries 148 definitions, theorems and abbreviations; the only dependencies are `propext`, `Classical.choice` and `Quot.sound`, or none. This is a review inventory, not an aggregate or new-theorem count. The audited code has no custom axiom, sorry, admit, native_decide or unsafe declaration. Imports contain no triple-family module. Six independent false assertions fail with Lean's explicit decide falsity diagnostic. A malformed proof of True fails on an unknown identifier and is excluded from those six; its clean twin passes.

Two failed reviewer attempts are retained and excluded from acceptance. `ReviewerChecks-attempt1.*` documents an incorrect `simpa` in the review test; the correction used an explicit rootedSpan equality before the existing connectivity theorem. The failed compilation's temporary sorryAx dependencies are not in accepted proofs. `audit_sources-attempt1.*` documents a raw token scan matching the word axiom in a comment; the successful scan strips Lean comments. No candidate source was edited to resolve either issue.

The independent checker and proof share the stated binary-tree/address specification, and the source compilation shares the Lean kernel and standard library. Those shared foundations are explicit. The broad finite panel's expected values come from the pre-source LCA instrument, not the candidate extractor. The author and other adversary receipts were read only after this independent derivation and checker were fixed. The project-wide `bootloops-check` suite was not run in this review; the complete relevant Lean dependency chain and exact finite panel were executed. No unavailable engine was required.

## Report review and final scope

The main report was reviewed with the prose and referee skills. Its final SHA256 is `cdefec22bc2d52d70a639754652faeed6a5b15b4895b0a9789a3358dd5d8f163`, retained as `REPORT-reviewed.md`. One low-severity ambiguity was corrected by the author: “one address has one label” now specifies functionality of leaf occurrences and conditional uniqueness for an occurring label. The final diff was read and the corrected sentence checked against TreeAddresses. The report's author/adversary counts agree with the cited receipts; these count checks are labelled reading rather than independent reruns. `referee_sim_REPORT.md` records audience, correctness and novelty objections and their answers. No unresolved issue remains in this report snapshot.

The accepted claim is the exact-source MinimalEmbedding constructor and its original region/consumer use. The bounded checks, ordinary LCA/path argument, source rebuild and semantic reading each retain their separate scope. Parent-owned theorem totals and broader bridge claims are unchanged by this review.
