# Frozen integration: hostile semantic and interface review

Date: 2026-10-15. Reviewer: fresh nonauthor agent. This is a source-bound semantic/interface pass, not another independent replication or a new theorem campaign. The three main milestones remain OPEN.

## Contract and scope

Allowed source identity: `AUTHOR-MANIFEST-FROZEN.json`, frozen at 2026-10-15T07:30:14.631964+00:00. Only the manifest-listed integration Lean sources, RESULT.md, FIRST-GAP.md, frozen imported core/geometry sources, and original RMAF are read as candidate evidence. The live cut-realization, coverage, profile/exchange/cherry-selection extensions and WORKFILE are excluded. Author replay scripts and receipts are not reused.

Method: read claims and exact theorem premises with line locators; distinguish source extraction from reviewer inference; seek finite witnesses to any stronger consumer interpretation. Broad declaration census and Lean replay are assigned separately and are not duplicated here.

## Incremental source notes

### Checker-to-source interface (read)

`SourceBridge.lean:306–311` has exactly two Boolean premises: `partitionCheck (leaves t) bs = true` and `pairwiseEmbeddings t bs = true`. The constructor at 243–267 proves actual support vertices, terminal ownership, connectedness by `Walk`, and disjointness. `minimalVertices_connected` (123–130) derives walks from the frozen geometry hull theorem; it does not receive connectedness as a premise. Original-label owner equivalence is the biconditional at 271–293.

The exact checker includes nonempty blocks, one flattened occurrence of each label occurring in the input, and no foreign labels (`RMAF.lean:149–152`). The source bridge and `checked_normalization_lift` do **not** need distinct input labels; that stronger requirement belongs to `generate` (`CoreProgram.lean:124–126`). They also do **not** claim agreement between two trees: `agreement` additionally checks the second tree and `restrictionAgrees` (`RMAF.lean:144–157`). A consumer must not replace those extra guards by the source-partition bridge alone.

`SourcePartition` itself allows arbitrary owner values away from terminals and supports with no terminal; it does not assert a finite number of blocks or component realization (`CoreGraph.lean:185–195`). Here `checkedSupport` is specifically a minimal embedding indexed by `bs.idxOf b` (`SourceBridge.lean:206–214`), so the construction is more specific than the abstract structure. The theorem's terminal owner biconditional is the warranted original-label fact, not a statement about owners at every original vertex.

Reviewer inference: the RESULT paragraph at 8–15 accurately scopes the bridge to the source checker. A general agreement-forest, finite-owner-count, or original residual-component conclusion would need additional arguments not present in this interface.

### Homogeneous normalization and original-label lift (read)

The frozen coarsening theorem has an actual cherry, an actual `SourcePartition`, monochromaticity and equal cherry colors as premises (`CherryCoarsening.lean:196–204`). Its construction can merge the two terminal owners and remove the cherry parent from a third support (`mergeSupport`, 13–16); the third support's connectedness is proved by the one-neighbor walk argument (56–71, 99–114). It does not assume the cherry parent was free. `Refines` means old equality implies new equality, not a biconditional (158–160).

`Contraction.lean:135–157` restricts supports to the surviving actual graph after same-block coarsening; its same-block premise is discharged at `Normalization.lean:133–137`. The new terminal at the cherry parent receives the old left terminal owner (104–108), and `contractPartition_owner` preserves every old terminal's owner after projection (164–177). Actual connectedness is proved by deleting excursions through both old cherry terminals before changing the tree (110–132).

The normalization consumer is exact: `normalize_gcontracts` follows every branch of the executable recursion (`Normalization.lean:168–187`), then composes the graph transports (189–207). `GroupedTransport` requires old payload **containment** in a new group plus forward preservation of terminal owner equality (99–105). It does not assert a bijection, equal owner identifiers across stages, payload list equality, or the converse implication from new owner equality to old owner equality. The initial original-label theorem has only the two checks and block monochromaticity as premises (`InitialLift.lean:117–126`); it gives every original leaf a normalized group containing its label and maps common-block labels to equal owners. `initialPartition` explicitly transports the original-label partition through recoloring without changing its owners or supports (33–47, 88–98).

Reviewer inference: RESULT 17–24 states this coarsening and containment scope accurately. Reading “preserves old block equality” as an iff would be false: homogeneous contraction deliberately permits two formerly different owners to merge. A same-colored two-leaf source with singleton original blocks is a finite witness to that stronger interpretation; it is not a counterexample to the stated forward implication.

### Chooser and exact attempt (read)

The `.one` consumer proves actual selected membership and a color-filter length of one (`Branches.lean:60–77`). The singleton theorem additionally requires distinct **origins** and monochromaticity (105–118). Distinct origins turn equality of selected group records into equality of occurrences (41–58); no assumption about distinct skeleton color labels is needed. The `.two` consumer derives an actual grouped cherry and unequal colors (175–199), then obtains **one of** the two singleton alternatives (203–210). It does not promise that both attempted branches preserve an arbitrary target partition. No-refusal is separately proved for `FullyNormalized` trees, and the executable normalizer establishes this predicate (212–226, 257–282).

`attempt_singleton_source` receives `origins.Nodup`, `RootZeroOnly`, and `CutsAvoid`, plus an actual nonroot grouped leaf and its singleton property (`CutRecords.lean:166–180`). `RootZeroOnly` means that `[]` does not occur below the display root (8–12); together with the nonroot display occurrence it excludes an empty **original** origin (96–108). `CutsAvoid` means every cut is absent from all current node/group origins (14–15); selected membership therefore excludes duplicates (181–182). `erase_leaf_realization` establishes a nonempty exact result under distinct origins (EraseLift.lean:40–87), discharging the final guard. The proof unfolds the literal `attempt` at 186.

The three premises are derived for the initial state (`Origins.lean:24–50`; `CutRecords.lean:22–34`, 254–257) and preserved by normalization and successful erasure (`Origins.lean:52–109`; `CutRecords.lean:36–94`, 148–161). `step_source_progress` takes those invariants as explicit premises at 209–212; it does not assume its `SourceAttempt` conclusion. It obtains the normalized partition and singleton branch before applying the exact attempt theorem (220–236). The first production-state theorem initializes the premises from `fromTree` and the Boolean checks (240–257).

Reviewer inference: the successful-guard claim in RESULT 34–40 is supported. The source-preserving branch is existential and target-partition-dependent; the executable chooser explores both `.two` candidates. The continuation `f` is unrestricted, and `SourceAttempt` certifies the invocation and local transported state, not any property of the receipt returned by `f` (`CutRecords.lean:190–202`).

Exact execution facts recorded for later use: `normalize` merges homogeneous child groups and concatenates payloads (`CoreProgram.lean:29–36`); `erase` deletes an entire matching internal origin as well as a matching group, then suppresses unary parents (38–46). `attempt` checks nonroot origin, duplicate cut, and nonempty erase before invoking the continuation (97–106). `run 0` still executes a step and uses a pruning continuation (118–122); budget totality alone therefore cannot imply output existence. `generate` clips the user budget to `leaves.length - 1` (124–126). Prefix/attempt bounds explicitly leave polynomial per-node work and reconstruction separate (230–237).

### Suppression and original-cut boundary (read)

`erase_leaf_source_transport` gives exact survival of unchanged group records, owner equality after a new-to-old display embedding, inverse survival of every nonchosen old group occurrence, and absence of the chosen owner from surviving terminals (`EraseLift.lean:163–180`). These facts concern the actual old/new **display skeletons**. The embedding has nontrivial address changes even when the original group origin remains fixed (`Suppression.lean:95–103`).

`erasure_path` maps membership in each new address path into the old path (Suppression.lean:141–189); it does not say that a new edge maps to one old edge. `erasePartition` constructs new supports as hulls of surviving old-owner terminals (191–233). Its image-in-old-support proof derives convexity from actual graph walks (45–55, 199–206), so this construction does not assume convex source supports or retain arbitrary leafless excursions. The frozen control explicitly has `[]` and `[false,true]` as images of adjacent new vertices, and proves they are not adjacent in the old tree (`Controls.lean:28–47`).

`reachable_origins_actual` has an origins-sublist premise and proves membership in the original vertex set (`Origins.lean:113–136`). Distinct and valid original endpoints cannot establish which original residual component contains the edge before the cut. No residual adjacency or cut-forbidden walk occurs in the stated local continuation result (`CutRecords.lean:190–219`). The original component bijection and exact leaf-label sets are explicitly the missing consumer (`FIRST-GAP.md:24–48`). Existing `GoodCuts` and `OutputShape` are syntactic invariants only (`CoreInvariants.lean:61–62`, 118–127, 166–173).

Reviewer inference: the original-edge and finite-budget caveats in RESULT 42–46 and FIRST-GAP 3–6 are correctly placed before the replay discussion. No original residual-component theorem follows from the display-graph path embedding alone. The additional work needed is exactly the reachability-derived residual invariant listed in FIRST-GAP 31–43, followed by finish/output identification at 45–48.

## Consumer and framing rulings

The top-level boundary is explicit in the frozen RESULT:

> “The complete source generator, original cut-component realization, and full 2.33 algorithm remain OPEN.” (`RESULT.md:4–5`)

The exact local theorem's comment also states:

> “The statement does not certify the original edge's residual components or that a finite cut budget reaches an output.” (`CutRecords.lean:207–208`)

The targeted use-site search covered all eleven frozen integration `.lean` files, with the relevant declarations and consumers opened above. It was not a declaration census. The consuming chain is:

| Delivered object | Frozen consuming sites | Premise ruling |
|---|---|---|
| Checked constructor and owner biconditional | `InitialLift.lean:88–112`, 127–138; `Controls.lean:13–20`, 51–58 | Exact hp/he proofs are supplied. Block monochromaticity is separately supplied when needed. The named existential `sourcePartition_from_checks` packages the same constructor; it is not itself an executable generator call. |
| Same-graph homogeneous coarsening | `Normalization.lean:133–145` | Actual contraction supplies an actual homogeneous cherry; monochromaticity is the theorem premise. The coarsening's same-owner conclusion discharges the quotient premise. |
| Quotient transport and composition | `Normalization.lean:189–207`; `InitialLift.lean:128–138`; `CutRecords.lean:220–224` | Each normalization rewrite is derived from the literal recursion. The map composes forward owner equality and payload containment. |
| Exact erase/suppression transport | `CutRecords.lean:181–186` | Selected occurrence, nonroot display address and singleton are obtained from choose; distinct origins discharges the exact erase realization. Additional local origin invariants discharge the two other attempt guards. |
| Singleton alternatives and no-refusal | `CutRecords.lean:225–236` | `.one` uses distinct origins and unique color; `.two` uses an actual mixed cherry. Fully normalized status is derived from normalize. |
| Local `SourceAttempt` conclusion | `CutRecords.lean:219`, 229–234, 253–257 | It is constructed, not assumed. Its continuation is arbitrary. No theorem in this searched integration chain consumes it to prove a budgeted `run` output or original residual components. |

The initial source theorems also apply to repeated original labels: neither their Boolean premises nor the fromTree origin invariants require `(leaves t).Nodup` (`SourceBridge.lean:306–310`; `InitialLift.lean:117–126`; `CutRecords.lean:240–257`). The executable `generate` wrapper independently rejects duplicate labels (`CoreProgram.lean:124–126`). For example, `t = node (leaf 0) (leaf 0)` and `bs = [[0]]` satisfy both source checks by their definitions but fail the wrapper's distinct-label guard. This is a direct finite source-reading inference, not an executed extra witness. Any report that says these source theorems prove acceptance of the complete `generate` call should state the distinct-label guard. The current RESULT does not make that claim.

The local theorem's premises do not include nonempty group payloads, their original-label purity, a global original-label partition, actual original vertex identities, or any accumulated detached/cuts length relation. FromTree and additional invariants can establish some of these facts, but an arbitrary local state satisfying the three origin guards need not satisfy them (W5). At finish, the local theorem concludes only the chooser's `.finish` equality (`CutRecords.lean:215–219`, 226); output syntax comes from `CoreProgram.step` (108–116), and semantic identification of that syntax with original residual components remains the missing consumer.

| Audience | Axis | Standard objection | Answer and severity |
|---|---|---|---|
| Formal verification readers | Correctness | Does the program derive the graph hypotheses, or merely accept a structure carrying the desired conclusion? | Checked supports are constructed from hp/he, normalization and suppression are constructed, chooser premises are derived, and SourceAttempt is a conclusion. Exact premises are listed above. No source-level defect identified in this pass. |
| Formal verification readers | Novelty | Does another compiler review become a new independent theorem replication? | RESULT 62–64 calls the author replay development evidence and requires fresh review. This pass is only semantic/interface review and uses the same frozen source mathematics. No new replication is claimed. |
| Graph algorithms readers | Correctness | Where do display singleton detachment and valid origin identifiers become a partition of original residual components? | They do not in this package. RESULT 4–5 and 42–46 disclose the missing theorem; FIRST-GAP 24–48 gives its quantifiers and finish consumer. No missing caveat on the opening reading path. |
| Graph algorithms readers | Novelty | Is the local cherry argument being presented as a complete new 2.33 algorithm? | The full algorithm remains open in RESULT 4–5; no priority or literature novelty claim is made. Literature novelty was not reviewed in this source-only pass. |
| Implementers using the generator | Correctness | Does a successful local step ensure a returned output within the requested budget, and is the implementation work bounded? | W3 excludes that inference. RESULT 44–46 and FIRST-GAP 50–60 retain coverage, realized cost, mass and per-prefix work as open. CoreProgram 230–237 limits its bound to prefix and attempted-child counts. |
| Implementers using the generator | Novelty | Which executable capability can be relied on beyond the existing generator definitions and syntactic counts? | The local interface supports exact normalization and successful source-preserving attempt invocation under explicit premises. Complete output coverage/cost/mass/work are unavailable. No comparative performance or prior-art advantage is established here. |

Framing assessment: no necessary edit to the frozen RESULT or FIRST-GAP was identified for these semantic boundaries. Preserve the word “local” and the existential branch scope in any later report. A title or lead sentence saying “source generator verified” or “2.33 algorithm verified” would overstate the delivered consumer.

## Executed hostile witnesses

Pre-execution plan: use only finite integer/list/address operations in a fresh source-derived Python model. The toolkit index and `emitall/GUIDE.md` were checked; emitall compares receipt claims but does not evaluate these GTree operations. A one-shot evaluator is warranted to expose stronger semantic readings, without changing or reusing author code. Its expected values come from the literal small constructions below. This is source interpretation plus a finite implementation check, not a separately derived mathematical model or another independent replication.

The fixed cases are: (W1) a caterpillar quartet's partition check passes while its two alternating hulls collide; (W2) two same-color singleton blocks merge under normalization; (W3) a two-leaf valid local attempt reaches the pruning continuation at budget zero and emits no output; (W4) a five-leaf mixed-cherry choice has exactly one singleton candidate for the supplied valid partition; (W5) a fabricated, unreachable display satisfies the three local origin guards but its selected origin is not a vertex of an independently named original tree. W5 will be labeled a counterexample to dropping reachability, never to a reachable-state claim.

Before these cases, the evaluator must recover the planted singleton and homogeneous two-leaf answers, and its exact comparison must reject one deliberately altered expected payload. All cases use fixed tiny trees; runtime is unknown until measured, with no long search or extrapolation planned. Failure of a prewritten assertion stops the run. No witness can refute a theorem whose premises it fails.

Execution (paths updated after relocation): `./bootloops-python research/rmaf/results/algorithm-integration-fresh-review-hostile-semantics-20261015.py research/rmaf/results/algorithm-integration-fresh-review-hostile-semantics-20261015.json`. The retained script/output are local and separately named from author evidence. All five fixed witness assertions passed; both planted answers were recovered and the corrupted expected payload was rejected. The measured model evaluation time was `0.00012433400024747243` seconds; this excludes interpreter/wrapper startup and supports no performance claim about the Lean program.

| Case | Executed result | Exactly which stronger reading fails |
|---|---|---|
| W1 | On `0,(1,(2,3))`, blocks `[[0,2],[1,3]]` pass partition coverage, but hulls intersect at `[true]` and `[true,true]`. | Dropping the pairwise embedding guard from `SourceBridge.lean:306–310`. |
| W2 | Two homogeneous terminal singleton blocks `[[5],[9]]` become one group `[5,9]`; both old leaf addresses project to `[]`. | An iff for block equality, or a block bijection through normalization. The stated forward transport holds. |
| W3 | On two differently colored leaves and singleton blocks, the erase succeeds at budget zero; the receipt has no output and no refusal, with one visited prefix, one attempt, and one prune. | Local successful continuation implies a budgeted output. The continuation is the literal pruning function in `CoreProgram.lean:120–122`. |
| W4 | On `0,(1,(2,(3,4)))` with parity coloring and valid blocks `[[0,2,4],[1],[3]]`, choose returns candidates `[3]` and `[4]`; only `[3]` is a target singleton. | Both `.two` candidates preserve an arbitrary target partition; the theorem promises an alternative. |
| W5 | A fabricated two-leaf display has distinct origins, `RootZeroOnly`, empty cuts and a valid singleton source partition; attempt reaches its continuation while the chosen original identifier `[false,false,false]` is invalid in the separately named original two-leaf tree. | Dropping reachability when importing the local theorem into an original-graph consumer. This display is explicitly unreachable and refutes no reachable-state assertion. |

These are executable finite witnesses in the fresh source-derived model. The shared mathematical layer is the frozen definitions and the reviewer's reading of them; the script is not a disjoint correctness oracle. No finite witness to failure of a stated frozen theorem was found in these cases. The broad kernel/module audit is outside this pass.

Lineage hashes: Python source SHA-256 `22d2df40af46414893661276904da273185ab106af01c87d04c08a8da993f430`; retained JSON SHA-256 `e49bae8eb63ce8907eec11577d1c02707f7de8b7870d3acf5fa909ba4a188edf`. The report was read again after editing, and its quoted scope sentences, finite counts, and theorem/continuation distinctions were checked against the opened sources and retained JSON. No rendered-PDF check was applicable to this Markdown review note.

Relocation record (2026-10-15): the two `algorithm-integration-fresh-review-hostile-semantics-20261015` files were moved from repository-root `results/` into `research/rmaf/results/`, preserving their basenames and contents. Both SHA-256 values above remained unchanged. No calculation was rerun; only the evidence locations and this review note changed.

## Review status

Source/interface pass complete. No contradiction to a stated frozen theorem was found by the inspected premises/use-sites and the five finite model witnesses. This conclusion is narrower than kernel verification, an independent replication, or a proof of the complete algorithm.

All three main milestones remain OPEN. The remaining obligations include original-cut component realization, finite-budget complete output/refinement coverage, and realized universal cost/raw mass/polynomial implementation-work bounds. No author script was reused and no frozen candidate source was changed. The independent broad declaration/kernel audit is assigned separately.
