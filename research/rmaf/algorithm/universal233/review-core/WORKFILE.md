# Fresh nonauthor core verification

Date: 2026-10-15. Scope: frozen core delivery only; no geometry/safe-cover/root proof artifacts read. Authoring ownership is confined to this directory. Target: `../../ALGORITHM-233-UNIVERSAL-TARGET.md`.

## Gate and independence
Pending: record shared specification, frozen input hashes, independent routes, plants, exact pass/fail conditions before controls.

## Frozen source and claims
Pending: inspect REPORT/FIRST-GAP and source modules one by one; transcribe substantive claim/interface findings here.

## Lean replay and axiom audit
Pending: fresh copied sources, build logs, complete declaration audit, prohibited-proof scan, source-bound false controls.

## Independent exact graph controls
Pending: one-shot fresh graph evaluator from Tree specification; known positive/negative controls before corpus search; homogeneous/mixed cherry and third-block parent checks.

## Program consumer trace
Pending: normalize/erase/cut call sites, hypotheses and realized-vs-syntactic cut/cost distinction.

## Claim verdicts and first gap
Pending: machine-readable perclaim scoped CONFIRMED/REFUTED/OPEN. Algorithm/Correctness/Smaller base remain OPEN.

## Initial record extraction (READ)

`core/REPORT.md` explicitly states "The universal source core remains OPEN" and does not claim full recursive coverage, original-cut realization, or runtime. Its substantive local claims are mixed-cherry singleton, unique-color singleton, homogeneous-cherry coarsening on actual graph walks, candidate structural work bounds, payload/purity preservation, and syntactic cut records. `core/FIRST-GAP.md` separately states the Boolean-checker-to-support interface and the first internal `step.normalize` quotient simulation as unsupplied. The input report's 112-declaration audit and nine controls are author execution receipts only, not adopted as independent verification.

Gate: rebuild frozen source copies under the pinned Lean runtime; independent declaration inventory and complete `#print axioms`; reject every theorem/axiom proof dependency beyond `propext`, `Quot.sound`, `Classical.choice`, and reject `sorry`, `admit`, `native_decide`, custom axioms. False controls must fail for falsehood specifically. Independently derive small graph supports without importing author's graph/program code; use exact graph/tree arithmetic and record all denominators. A finite no-fire is scoped finite evidence only. Runtime/Mass/Coverage/Algorithm remain OPEN absent universal bridge theorems.

Independence ledger: frozen Lean sources are production-side inputs; rebuilding them is fresh execution, not an independent proof derivation. Fresh Python controls will share only `RMAF.Tree`'s rooted binary-tree specification and the mathematical statement; no author's graph evaluator or prototype code will be imported. Report and FIRST-GAP were read as claim extraction contact. None of unfinished geometry/safe-cover/root proof artifacts has been read.

## Local graph interface extraction (READ; frozen replay source)

`CoreGraph.lean:189–195` defines owner/support/actual/terminal_exact/connected/disjoint only. Supports may be empty, leafless or contain surplus vertices; finite actual graph still makes the surgery statement meaningful. No partition coverage, source cuts or generator property is assumed. `mixed_cherry_singleton:230–242` uses actual leaf adjacency and common-parent occupancy, with monochromaticity and unequal child colors; its conclusion is singleton **among actual current leaf occurrences**, not detachment simulation. `unique_color_singleton:246–251` assumes uniqueness among occurrences rather than merely a color count on stale groups.

`CherryCoarsening.lean:196–204` proves existence of Q on the **same** unsuppressed `RMAF.Tree`, with owner-equality implication `Refines` (`:158–160`), monochromaticity and merged cherry owners. Explicit support surgery (`:13–16`) unions supports a,b plus parent for a, empties b, and removes parent from all other supports. The third-block connectivity proof (`:110–114`) uses the proved at-most-one-neighbor property (`:56–71`) and `Walk.avoid_one_neighbor` (`CoreGraph:78–101`); parent occupancy is not ruled out by a hidden premise. This does not construct normalized grouped graph Q or identify components of recorded cuts. Exact finite controls and fresh Lean replay pending.

## Program and invariant interface extraction (READ)

`CoreProgram.lean:120–126` uses finite budget recursion and caps initial q at leaves−1; q=0 still visits/normalizes/selects and counts every attempted continuation as a pruned prefix. `attempt:97–106` counts root/duplicate/invalid-erase rejection attempts as 1, and successful continuation as childAttempts+1. `step:108–116` branches at most twice. `run_visited_exponential:180–183`, `run_attempts_bound:224–228`, `run_prefix_work_bound:233–237` apply to **arbitrary** GTree/detached/cuts, no graph-validity precondition. Thus they really bound the instrumented production tree, including pruned attempts; they do not count per-node normalize/choose/list-copy costs.

`CoreInvariants.lean:61–62` GoodCuts means only syntactic address Nodup/nonempty; `generate_cut_records:120–125` does not certify actual source vertices. `OutputShape:127` is only list-length equality; `generate_recorded_charge:168–173` certifies it, not graph components, label partition validity, nonredundancy, realized cost lower bound or mass. `normalize_payload:12–24` and `normalize_pure:36–59` are appropriate payload/color claims, not graph simulation.

Consumer trace pending report: normalize at CoreProgram:110 needs expanded-label coarsening plus quotient map; unique-color choice at :113 needs reachable current leaf bijection/purity/uniqueness and erase simulation; mixed choice at :114 needs genuine normalized current cherry with unequal colors, support singleton alternative and erase simulation; cut record :105 needs valid nonroot original edge, leafbearing residual components and partition lift. None is discharged merely by the local theorem or prefix counts.

New-code justification: tools index capability search found no rooted-tree support/Lean audit instrument; cosmoflow/dogtag are Feynman graph domain tools. This review uses one-shot local scripts, deliberately disjoint from author evaluators, wrapping existing pinned Lean instead of altering toolkit code. Runtime unknown; start with Lean trivial known-truth compilation and n<=4 graph pilot, retain per-phase monotonic timings. No long computation authorized without measured projection.

Executed fresh independent graph pilot (`graph-pilot.log`): n=2..4, 8 ordered shapes, 3,629 internal assignments, 317 valid support assignments, 2,779 monochromatic colorings. No local-claim failure. n=4 completed in 0.02259s. n=5 candidate assignment upper bound from same representation is ≤14*52*6^4=943,488 (less than 268 times n=4); even pessimistic linear projection from measured n=4 is <7s. Proceed n=5, bounded 90s. This is a bound for the chosen finite review only.

Lean source replay modules all compiled; false controls rejected. Reviewer audit metaprogram initially failed due to unparenthesized Name-quotation syntax, before auditing any record; retained `FreshAudit-first.log`. This is an infrastructure error, not a theorem/axiom verdict. Fix and replay from source.

Fresh exact graph census (`graph-census.log`, source-hashed `graph-controls-n5.json`) completed through n=5 in 1.0548s for the n=5 tier: 22 ordered shapes, 216,107 support assignment candidates, 3,319 valid terminal-exact connected/disjoint supports, 84,267 monochromatic colorings. Checks: 75,063 mixed-cherry alternatives, 110,806 unique-color occurrences, 42,992 homogeneous coarsenings including 3,896 third-parent cases. No fire against scoped local claims; no inference to universal coverage. Nine corruption/misleading-claim plants caught; explicit leafless-support and root fixtures passed. (Counts will be independently summed from JSON before report.)

Reviewer audit pilot timed out at 90s because `.eraseDups` was mistakenly applied to the entire imported Lean environment before namespace filtering. Retained timeout log; reorder filter before deduplication (only delivered namespaces then remain). This is an infrastructure bottleneck and is not accepted as axiom evidence. Additional operational Lean controls now compiled: crossed q=0/1/2/3 gives (visited,attempts,pruned,outputs)=(1,2,2,0),(3,4,2,0),(5,4,0,2),(5,4,0,2); root/duplicate/whole-source failure attempts each count (0,1,0,1). A Lean fake Output satisfies GoodCuts and OutputShape with a nonexistent source vertex, demonstrating exact interface insufficiency. Initial reviewer elaboration errors retained in ReviewOperational.log; corrected file compiled in ReviewOperational-second.log.

Fresh corrected complete environment audit succeeded in 0.8957s (timing JSON retained). It enumerates imported and local delivered namespaces before auditing all transitive dependencies; includes generated constructors/recursors/equations, rather than trusting the author's explicit declaration count. Custom-axiom plant rejected with exact `REJECT_CUSTOM_AXIOM` marker; deliberately removed audit record rejected by parser; clean True twin compiled. Complete count and permitted axiom union will be read from verdict/log in report. No toolkit-wide suite run. A cold local Lake build over the same source copies follows to verify module build resolution, with no external packages. Initial Lake invocation used wrong relative paths before writing local config; retained lake-build-first.log; corrected cwd-relative config follows.

Audit completeness correction: module-origin enumeration found 47 compiler-private declarations not covered by the 574-name namespace audit. Their names begin `_private`, despite no explicit private source declarations. The module-origin pass audited all 621 declarations (422 core, 199 RMAF dependency), including these 47, with the permitted standard axiom union. The initial equality assertion correctly fired on the coverage difference; this is an audit instrumentation correction, not a theorem failure. `module_review.py` retains a reproducible full-origin inventory and tests both missing-record and an intentionally custom-axiom imported module outside the named namespaces. Earlier 574 count is superseded as completeness evidence.

Correction to preceding graph journal count: `graph-controls-n5.json` contains **8** graph corruption/misleading-claim plants, not nine; independently summed counts above agree exactly. Three Lean false propositions and two audit corruption controls are separate.

## Final scoped result

`REPORT.md`, `INTERFACE-TRACE.md` and `claims.json` are complete. The claim table has 26 scoped rows: 14 CONFIRMED delivered local/formal/executable statements, 3 REFUTED stronger misleading-claim plants, and 9 OPEN universal obligations. Algorithm, Correctness and Smaller base remain OPEN. First external gap: checker-to-connected-support conversion. First internal gap conditional on that conversion: CoreProgram.step:110 normalize quotient plus original-label refinement lift; erase and original-cut realization remain separate.

Complete module-origin inventory: 621 declarations = 422 core + 199 RMAF, including 47 compiler-generated private declarations absent from the initial namespace pass. Only `propext`, `Quot.sound`, `Classical.choice` occur. Custom-axiom-outside-namespace and missing-record plants rejected; three source-bound false propositions rejected specifically as false by decide; clean True twin compiled. Cold Lake compilation completed (12 jobs). Operational controls and independent graph controls are retained with their sources/logs. All explicit review writes remain under review-core; runtime wrappers recorded their ordinary dashboard history.

Prose checks: read REPORT and interface trace for meaning and hypothesis scope, then separately checked numerical/source consistency and wording. Corrected the graph-plant count from a journal typo to eight, replaced the incomplete namespace-audit claim with the module-origin total, and removed misleading quotation/heading wording. Machine checks recomposed all audit counts and compared every reported census count against JSON. These are local editorial passes; no claim of an independent outward-facing referee review is made.

Reproduction sources: replay_review.py, module_review.py, exact_graph_controls.py, make_claims.py. No geometry/safe-cover/root proof artifacts read; no full toolkit-wide suite, external compute, publication, hosting or novelty work performed. Original protocols, source proofs, author receipts, failed controls and upstream verification scripts remain unchanged.
