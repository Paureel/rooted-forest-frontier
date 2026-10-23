# Fresh review of universal merge

The exact universal merge interface is **CONFIRMED** by this nonauthor review. I reproduced the frozen finite controls with new code, rebuilt the pinned Lean modules and their local imports in an isolated directory, inspected their proofs and actual axiom output, and compiled a consumer of the existential support contract. The accepted result concerns two actual `CostRoute.Family` inputs whose designated indices are their boundaries. Restriction, completeness of the four-transition correspondence, color/mask legality, executable graph correspondence, automaton instantiation, Python refinement, and full G2 remain open. This review makes no novelty or runtime claim.

The separate geometry route is also confirmed for its 17 supporting statements. It supplies support geometry and label/disjointness interfaces; it does not construct a complete indexed output family or prove count/cost equations. The separate index route was neither opened nor awaited during this review. Any overall protocol grading across the supporting routes remains the parent's responsibility.

## Exact interfaces

`FiniteSelection.lean:18` constructs a `FiniteIndex` of the selected subtype. Its complete list contains every subtype member, and its nodup proof prevents duplicated indices. `FamilyMerge.lean:8` uses `Sum I {j : J // j ≠ p}`. The left boundary index represents the merged block; every other left index and each remaining right index retains its own tagged identity. The source does not identify indices by their labels or colors.

The concrete `merge` at `FamilyMerge.lean:45` returns an actual `Family`, proving boundedness, convexity, a leaf per index, pairwise disjointness, leaf coverage, and exact root ownership. Its finite enumeration is the old complete left enumeration plus the selected right enumeration. Child convexity and actual root ownership establish merged convexity through `ConnectedRegions.rooted_region_decomposition`; no output family or count equation is assumed. The import chain is acyclic:

`MergeControls → MergeContract → FamilyMerge → FiniteSelection → FamilyAssembly → ConnectedRegions → TripleDP → Std`.

`MergeContract.lean:61` explicitly exports the existential family and all exact supports. Its defining support clause is:

> `A.support (.inl o) = (fun a => a = [] ∨ liftSupport false (f.support o) a ∨`
> `  liftSupport true (g.support p) a)`

The same theorem exports unchanged lifted support functions for every surviving index, `A.boundary = some (.inl o)`, `A.blockCount = f.blockCount + g.blockCount - 1`, and `A.cost = f.cost + g.cost`. This package contains the support equalities a consumer needs. The earlier `normalized_assembly_exists` existence/count/cost package is not used to infer those equalities.

The concrete constructor requires `[DecidableEq J]`; the universal theorem has no such premise and chooses classical equality in its proof. The compiled `main_snapshot/InterfaceProbe.lean` consumes only `merge_universal`, without unfolding `merge` or assuming decidable equality. It extracts complete/nodup indexing, root ownership, merged label union, and both numerical equations. Actual printed types are retained in `triple-family-transitions-fresh-InterfaceProbe.log`.

Repeated labels cause no loss of leaf occurrences: `FamilyAssembly.LeafAt` uses vertex addresses, and all support equalities hold at every address. The `hasLabel` theorems at `MergeContract.lean:28`, `:36`, and `:44` state label membership and union; they do not assert label multiplicity. Unused internal vertices remain permitted by `Family.covers`, which covers leaves only, and the exact support equations prevent adding such vertices during merge.

## Executed controls

Before opening any new proof or author/adversary checker body, I wrote and hashed `exact_graph_checker.py`. It imports only Python standard-library modules. It constructs an undirected tree and checks induced-support connectivity, boundedness, leaf-bearing regions, disjointness, coverage, boundary ownership, exact supports/indices and numerical equations. Expected supports and numbers came from the frozen specification, never from this computed construction.

| Frozen controls | Result |
| --- | --- |
| Positive fixtures | 5 accepted with exact support, label, count and cost comparisons |
| Malformed input families | 4 rejected as outside the merge regime |
| Wrong numeric propositions | 4 rejected; all 4 clean twins accepted |
| Support corruptions | 3 rejected; all 3 clean twins accepted |

A supplementary repeated-label fixture preserved three leaf vertices in two indices, with cost one. A second supplementary control inserted an unused internal vertex: geometric family validation still passed, but exact-support comparison rejected the change. The separate false-proposition run asserted that deleting the T1 root preserves validity; it exited with an assertion naming disconnected support and wrong boundary ownership. Its immediately preceding clean assertion passed.

Receipts are `research/rmaf/results/triple-family-transitions-fresh-controls.json`, `-pilot.json`, and `-false-proposition.log`. The complete finite battery measured 0.000553 seconds internally after a one-case pilot; this timing excludes wrapper startup. These controls support the checker and interpretation of the theorem. They do not prove the universal statement or a formal graph-to-Lean equivalence.

## Kernel evidence

Both isolated rebuilds used `./bootloops-lean`, Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, on arm64-apple-darwin24.6.0. `ELAN_HOME` was the workspace `.runtime/elan`; each `LEAN_PATH` named only its new reviewer snapshot. Local `.olean` files were built from copied sources, never copied from author builds. All main pinned source hashes matched before and after execution.

| Module | Actual axiom-query outputs |
| --- | ---: |
| TripleDP, old dependency | 19 |
| ConnectedRegions, old dependency | 8 |
| FamilyAssembly, old dependency | 17 |
| FiniteSelection | 4 |
| FamilyMerge | 9 |
| MergeContract | 7 |
| MergeControls | 15 |
| InterfaceProbe, reviewer-only consumer | 1 |
| MergeGeometry, separate supporting route | 17 |

Every main-chain query used only `propext`, `Classical.choice`, and/or `Quot.sound`, or no axioms. The geometry theorem queries used only `propext` and/or `Quot.sound`, or no axioms. Source scans found no `sorry`, `sorryAx`, `admit`, `native_decide`, custom axiom declaration, `unsafe`, or `implemented_by` in the rebuilt proof chain. Counts above describe actual per-module queries; repeated builds and dependency replays add no theorem inventory entries.

The four pinned false numeric files failed at exactly `T1.cost = 1`, `T1.blockCount = 2`, `T3.blockCount = 1`, and `T4.cost = 6`. Four separate files with identical imports and respective correct values 0, 1, 3, and 3 compiled. A missing-import file failed before proving its proposition and was explicitly excluded from mathematical rejection evidence.

My first diagnostic matcher expected different Lean wording, and the first geometry matcher expected the pre-simplification proposition. Both stopped without crediting the negative test. I preserved those reviewer attempts, corrected the exact diagnostic matching, and completed the corrected runs. Geometry's reduced false goals are `¬True` and `[true] = [] ∨ [true] = [false] ∨ [true] = [false, true]`; both failed, and their separate same-import polarity-correct twins compiled. Seven geometry positive examples compiled before `MergeGeometry`.

## Claim-by-claim ruling

Locations below refer to the unchanged pinned `transitions/REPORT.md`, SHA256 `8a1b64ee1ad5be7fa195381de5ca4ca468ce166bfe28f2f5fd15301c4ee7b5a1`.

| Report location | Claim and ruling |
| --- | --- |
| Lines 3–6 | Actual merge, supports, label unions, count/cost: confirmed. “Fresh … review is pending” accurately describes the pinned earlier checkpoint; this addendum completes the main review. Restriction/full correspondence remain open. |
| Lines 8–15 | Complete/nodup selection and asymmetric survivor indexing: confirmed by `FiniteSelection:18–41`, `FamilyMerge:8,48`, and the actual old `FiniteIndex` fields. Equal labels/colors do not enter index equality. |
| Lines 17–22 | Exact supports and every output family field, without output validity assumptions: confirmed by `FamilyMerge:11–149` and `MergeContract:8–26`. |
| Lines 24–31 | Exact count/cost, exported existential support equations, premise distinction: confirmed by `FamilyMerge:151–175`, `MergeContract:61–76`, and the compiled consumer probe. |
| Lines 33–40 | Earlier X0 observations: retrieved from retained adversary receipts. The bounded receipt records 192 pairs; the mutation receipt records four missed numeric detections and exit 1. I verified all seven relocation hashes. I independently reproduced the frozen controls, but did not re-enumerate those 192 pairs. |
| Lines 42–43 | Main per-module query counts: independently reproduced exactly, as above. |
| Lines 44–48 | Five constructed Lean controls, four exact false propositions with correct values, malformed-import exclusion: independently reproduced. The main Lean controls test selected support facts; full exact fixture support comparison is additionally supplied by the fresh checker. |
| Lines 49–52 | Retained author receipts exist and distinguish accepted negative goals from the rejected import-error control. Fresh receipts independently establish the accepted source/axiom conclusions. Failed development elaborations are excluded. |
| Lines 54–58 | Separate geometry interfaces: confirmed by source and fresh kernel rebuild. Main imports none of that source. Authorship/read-order independence is reported provenance, consistent with the import/source records, not something the Lean kernel proves. No ruling is made on the active index route. |
| Lines 60–64 | Remaining obligations and excluded broader claims: appropriately scoped. Fresh review of the main merge is now complete; all stated scientific extensions remain open. |

`geometry_route/REPORT.md:13–43` matches the proved supporting interfaces. One premise deserves literal reading: `jointSupport_rootPaths` specifically requires the left witness `s []`; the intended two-boundary application supplies it. The report's phrase about either child boundary must not be consumed as a theorem with only `t []`. No such unsupported use appears in the main proof, which imports none of this route.

## Provenance and limits

The fresh checker SHA256 is `0ae2eb9a50f12eee9fcdd6b686f40132dd511e76f05b267b085f487fc76b76aa`; controls SHA256 is `4bb9a4893e3a879fa8a132b82e184eb81976f3bc244678457e92d122f6dde00b`. Full source inventories are in `main-source-manifest.json` and `geometry-source-manifest.json`; the final review file/receipt hashes are in `FINAL-SHA256.json`. Every geometry source also matched the retained author final source snapshot.

Independent authorship and no code reuse are recorded in `WORK.md`. Shared layers are the frozen target/fixtures, binary-address/tree interpretation, Python standard library, and the existing Lean/Std semantic modules. After freezing and running the fresh checker, I read the prior adversary report and receipts; I never read or imported its checker bodies. The graph checker and formal proof use different mechanisms, but a formal equivalence between their semantics remains outside this review.

I changed only reviewer-owned files and result receipts. Original author reports and pins remain unchanged, including their historical pending-review labels. The general BootLoops validation suite was not run: scoped fresh Lean compilation and exact-control execution were used for this proof-only review. No unavailable engine or platform limitation affected these scoped checks.
