# Fresh leastness and semantic/use-site review

Status: OPEN. Fresh nonauthor review of `LEASTNESS-TARGET.md`; no candidate sources or prior checker code read yet.

## Workflow and provenance
Target read first. Deviation: applicable skills/tool index were batch-read before this skeleton, producing truncated output; unread portions will be re-read individually. All authored review artifacts stay in this folder. Candidate sources will not be edited. Independent controls and LCA derivation must be frozen before source inspection.

## Frozen independent specification
Pending: exact address semantics, selected occurrences, LCA hull, leastness derivation, and positive/negative controls.

## Controls and pilot
Pending: independent Python instrument, positive controls, malformed-proof diagnostic; pilot before exhaustive bounded comparison.

## Candidate source contract
Pending: exact source hashes, proof assumptions, no custom axioms/sorry/native_decide, imports and source parity.

## Semantic and constructor field trace
Pending: valid nodes, leaves, labels, unique-labelled Instance; actual MinimalEmbedding fields.

## Rebuild and interface trace
Pending: fresh dependency rebuild and unchanged region/consumer composition, exact false Lean controls.

## Referee and prose review
Pending: main REPORT.md snapshot and objections on actual reader path.

## Verdict
OPEN: no scientific closure claimed.

## Independent control receipts (pre-source)
Frozen spec SHA256 `50482f86856d2904569e6e22d1be8061de83c265af90ad3da1543d9476035af8`. Independent script SHA256 `361767017ea2fe4825efbfcc1660a046648af8df4555d508cbc702fe3d005752`. Controls: 11 literal fixtures plus 6 corruptions with passing twins, all passed. Pilot through 2 leaves: 42 cases, 36 connected supersets, 0.0011851659983221907 s including controls. Second pilot through 4 leaves: 714 cases, 1863 connected supersets, 0.022264082999754464 s. Per-leaf block timings: n=3 112 cases / 0.0012894169994979165 s; n=4 560 / 0.01976216600087355 s. n=5 has 3136 cases and at most 4 times as many support subsets per case, projecting <1 s under this explicit subset-count scaling. A 30 s bound is sufficient for the next run; completed case count, not process activity, determines progress. These are finite graph checks only.

## Read: TreeAddresses semantic contract
`address_semantics/TreeAddresses.lean` lines 10–17 defines `vertices` by traversing actual children and `terminals` by selected label membership at each leaf, with false=left and true=right. Lines 20–31 independently declare actual-subtree-valid vertices and labelled leaf occurrences. The exact claims are `v ∈ vertices t ↔ ValidVertex t v` (33–64) and `v ∈ terminals selected t ↔ ∃ x, LeafOccurrence t v x ∧ x ∈ selected` (66–99). These match the frozen interpretation, including repeated labels. Occurrence label functionality is unconditional (133–138); converse address uniqueness explicitly requires `(leaves t).Nodup` (153–168). Instance uniqueness derives that condition from permutations of `List.range` (176–206), separately for each tree. Nothing identifies left-tree and right-tree addresses. Terminal/ambient lists have no repeated addresses even with repeated labels/selection (233–249). Imports: only RMAF. These are source-read assessments pending fresh compile and source hash check.

## Read: actual constructor
`lean/ActualEmbedding.lean` 9–23 returns the original `MinimalEmbedding`, with only tree, selected labels and a witness label occurring in both as inputs. Ambient and terminal fields are the actual traversal definitions (11–12). Nonempty terminals uses semantic occurrence existence (13). The support is `extractedSupport` from completed executable connectivity, supplied its proved nonempty witness (14). Ambient membership uses `minimal_in_vertices` after exact support rewrite (15–17); terminal inclusion uses `terminals_in_minimal` (18–20); leastness calls `minimal_least` for every connected support containing terminals (21–23), stronger than the structure's ambient-restricted quantifier. Exact support is list equality, not merely an isomorphism (33–36). Original region membership is rewritten to `minimalVertices` (47–52). `embedding_consumer` actually calls `MinimalEmbedding.deepest_root_in_neighbor` (56–65), requiring root depth order and explicit coordinate overlap. Its comment (54–55) disclaims semantic cross-tree transport. Need inspect imports and support structure to finish field trace, then compile.

## Read: leastness derivation
`lean/ExtractorLeastness.lean` imports only TreeAddresses and ExecutableConnectivity (1–2). Source route matches the frozen recursion: rooted-span output has a terminal descendant (25–63); terminals are in rootedSpan (65–75); span vertices are actual vertices (77–101); minimalVertices is a subset of span (103–117). From these, emitted vertices have terminal descendants and are ambient-valid (119–126). Terminal inclusion in minimalVertices is proved inductively through both initial-root suppression branches (129–149). The load-bearing LCA statement is `minimal_below_common_ancestor`: any common prefix of all selected occurrences prefixes every extractor vertex (176–209); the two-child case forces the common prefix to be empty using actual terminals in both children. The universal leastness proof (213–220) takes an arbitrary ConnectedSupport with terminal inclusion, obtains one terminal below the emitted vertex, proves the other support's shallowest root prefixes that vertex, and applies the original region's path convexity. No target property is an input. This avoids assuming an extractor-hull equality, and proves a stronger ambient-unrestricted inclusion within the global address graph. Finite independently derived LCA/intersection audit: 3850 cases and 16373 feasible connected supports through five leaves; all 17 controls pass, 0.37817037499917205 s (`lca-check-5.json`). No finite result is being called universal.

## Read: original GraphRegion structure and consumer
`../lean/GraphRegion.lean` 9–14 uses undirected append-one-bit adjacency and finite walks restricted to support membership. `ConnectedSupport` (87–91) is nonempty by its first/rest representation and requires every pair connected by such walks. `toRootedRegion` (106–112) derives below/convex from graph walks and a minimum-depth vertex; neither is assumed as a support field. The actual `MinimalEmbedding` (145–155) has ambient, terminals, nonempty terminals, ConnectedSupport, support-to-ambient inclusion, terminal preservation, and leastness over every ambient ConnectedSupport containing terminals. All fields align with ActualEmbedding's constructor. `region` (159–163) retains exact support membership. Its unchanged consumer (165–170) takes only two embeddings, depth ordering, and explicit shared address; it delegates to the graph-support and PureBridge consumer. Thus minimality is filled but not consumed by this particular region theorem. It cannot establish transport across distinct input trees.

## Read: completed executable support
`executable/lean/ExecutableConnectivity.lean` imports RMAF and GraphRegion (1–2). `Connected` is pairwise graph walks (10–11). The proof of `minimalVertices_connected` follows the unchanged extractor's three branches (109–127), and occurrence of one selected leaf yields nonempty output (151–167). `extractedSupport` takes exactly the head/tail of that output and proves its walk field by the list head-tail identity and connectivity (170–177). `extractedSupport_exact` states literal list equality (179–182). Thus the support field in the new constructor introduces neither lost vertices nor a surrogate graph. The preexisting exported region/consumer also uses exact output membership (184–204).

## Read: unchanged source and original region logic
`research/rmaf/lean/RMAF.lean` defines binary trees at 8–11, leaves at 13–15, and `Instance` labels as permutations of range at 19–24. The exact extractor recursion at 116–133 matches the pre-source frozen expectation, including suppression of all initial ancestors above the selected LCA and retention of internal unary paths. `PureBridge.lean` imports Std only; its RootedRegion interface (14–19) and original deepest-root theorem (23–31) require two prefixes of a shared coordinate, compare their lengths, and apply convexity. The rest of PureBridge has separate exchange assumptions (67–80), not derived by the new embedding. The only source imports in this audited chain are Std, RMAF, PureBridge, GraphRegion, ExecutableConnectivity, TreeAddresses, ExtractorLeastness. No triple-family import is in this chain.

## Fresh compilation pilot
Seven sources copied into `build/` and pinned in `source-manifest.json`; final TreeAddresses SHA256 equals the required `f2bbd08201b98893a0e824f041e9af72761933d7f29b4e9a89088d9d9e46fdb0`. RMAF pilot compiled in 5.496704916999079 s with source SHA256 `4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9` (`build-pilot.json`, `RMAF.log`). Full driver sets LEAN_PATH only to this review's build directory, preventing consumption of prior project oleans. At six remaining modules, assuming per-file cost comparable to this pilot suggests tens of seconds; actual timings will be retained individually with a 60 s per-module limit, and no hours-long run is planned. Progress is successful module count and explicit errors, never process status alone.

## Completed independent build and additional checks
All seven final-source modules compiled in `build/`; see `build-pilot.json` and `build-main.json`. The fresh reviewer module `ReviewerChecks.lean` compiles and restates the exact object, uses every original structure field, and calls the original consumer. It includes the 11 frozen support values and 11 frozen terminal values, occurrence-duplication controls, unconditional label functionality and two separate Instance uniqueness results. It positively proves the extra-root support connected/ambient/terminal-containing but nonleast, path deletion disconnected, invalid ambient rejection, and missing terminal rejection.

The first reviewer test failed at a `simpa` that unfolded the goal differently from its source theorem. The corrected test rewrites a literal rootedSpan equality before invoking its connectedness theorem. Both failed source and log are retained in `ReviewerChecks-attempt1.*`; the failed compilation introduced temporary `sorryAx` placeholders and contributes no accepted proof. The successful final test has only the three standard axiom names.

`source-audit.json` records current/snapshot equality for all seven modules and historical equality of RMAF/PureBridge/GraphRegion/ExecutableConnectivity against the completed checkpoint. All 148 definitions/theorems/abbreviations in the seven-module source chain were queried with `#print axioms`; only `propext`, `Classical.choice`, `Quot.sound` occur. This is a whole-chain review inventory, not a count of new project theorems. A code-token scan found no custom axiom, sorry, admit, native_decide or unsafe declaration. The initial raw scan matched 'axiom' in a PureBridge comment; its retained failed attempt was corrected by stripping Lean comments before scanning. Six separate false source assertions each receive the explicit decide falsity diagnostic. The malformed proof of True receives an unknown-identifier diagnostic, is excluded from the six, and its clean True twin succeeds.

## Additional exact-source finite panel
The frozen independent LCA/reference family is also compiled directly against RMAF and TreeAddresses. Each generated theorem checks both support and terminal-list equality by kernel `decide`, followed by an axiom query. Pilot n≤2: 42 cases / 84 equalities / 0.4808510410002782 s, with all 42 declarations reporting no axioms. A second pilot at n≤4 measures scaling before the full n≤5 run. These outputs are derived from the original pre-source checker; generating Lean syntax does not change the frozen expectations.
The second source-panel pilot completed 714 cases / 1428 equalities in 4.289785707998817 s. All 714 axiom queries are empty. Scaling by case count, with a 1.5 factor for the increase from four to five leaves, projects about 35 s for the 3850-case panel; the explicit 60 s timeout remains. This is an estimate from these two measured pilots, not a completion promise.
