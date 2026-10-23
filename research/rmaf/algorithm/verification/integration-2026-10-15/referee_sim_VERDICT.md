# Framing and consumer review

The scoped conclusions in `VERDICT.md` agree with the frozen interfaces opened
for this review. No HIGH or MEDIUM scientific or framing defect was found.
The report owner applied both LOW wording corrections and I verified the
revised report and trace. Neither correction changes a mathematical ruling.

This is a fresh framing review within the existing reviewer lineage. I read
the source premises and consuming calls and retrieved the retained receipts.
I executed no Lean replay, declaration census, finite-control evaluator or
semantic witness. This review adds zero independent replications and no
theorem progress. All three main algorithm milestones remain OPEN.

## Reviewed records

The reviewed source identity is `AUTHOR-MANIFEST-FROZEN.json`, SHA-256
`e4b8f631a98a1c059656da04e497d66e7703d076e18b7db9a22d86e98ad3ca93`.
Every candidate source opened below is an exact path listed in that manifest.
Source basenames in this audit resolve as follows:

- Integration sources, `RESULT.md` and `FIRST-GAP.md`:
  `research/rmaf/algorithm/universal233/integration/`.
- `CoreGraph.lean`, `CoreProgram.lean`, `CoreInvariants.lean` and
  `CherryCoarsening.lean`: `research/rmaf/algorithm/universal233/core/`.
- `RMAF.lean`: `research/rmaf/lean/RMAF.lean`.

I also opened `CONSUMER-TRACE.json`, `EVIDENCE.json`,
`AXIOM-INVENTORY.json` metadata, `semantic_referee.md`,
`COMPARISON-MAP.json`, `ADAPTER-FAILURES.json`, `SOURCE-CONTACTS.json`,
the pre-candidate receipt and kernel-control pin, and the named review
receipts/logs under `research/rmaf/results/algorithm-integration-fresh-review-*`.
Review-generated Lean scope witnesses and diagnostic logs were read as
evidence records, not as frozen candidate theorems. I did not read the live
cut-realization, source-coverage, profile/exchange/cherry-selection extensions,
the main WORKFILE, or unfinished research. I edited only this audit note.
The report owner's wording corrections are recorded below; no frozen readiness
file, candidate source, expectation or execution receipt was changed.

## Source findings

The following facts were read directly; the quoted fragments were checked
against the opened source bytes.

| Claim | Frozen locator and exact boundary | Ruling |
|---|---|---|
| Checker-to-source constructor | `SourceBridge.lean:243–267,306–311` takes only the two exact Boolean checks. Its `connected := by` field at 253–260 constructs walks from `minimalVertices_connected`, whose proof at 123–130 derives convexity and connectedness. | Actual supports and connectedness are conclusions. Neither two-tree restriction agreement nor complete `generate` acceptance follows. `RMAF.lean:154–157` contains the additional agreement guards; `CoreProgram.lean:124–126` contains the distinct-label wrapper guard. |
| Original owner equivalence | `SourceBridge.lean:271–276` quantifies actual `LeafAt` occurrences. Equality of the two checked owners is equivalent to the labels sharing a supplied block, expressed as `∃ b, b ∈ bs ∧ x ∈ b ∧ y ∈ b`. | The biconditional concerns original leaf occurrences. Arbitrary nonterminal owner values remain outside it. |
| Homogeneous coarsening and quotient | `CherryCoarsening.lean:13–16,99–114,196–204` permits the parent in a third support and proves the remaining support connected. `Contraction.lean:135–157` takes equal cherry owners; `Normalization.lean:133–145` derives that premise by coarsening before constructing the quotient. | The report correctly identifies a constructed coarsening and actual quotient. It does not smuggle in a free-parent or preexisting same-owner assumption. |
| Normalization payload/owner lift | `Normalization.lean:99–105` requires `∀ x, x ∈ g.labels → x ∈ a.labels` and only `P.owner v = P.owner w → Q.owner (f v) = Q.owner (f w)`. The literal recursion is related to contractions at 170–187 and composed at 189–207. `InitialLift.lean:117–138` supplies the original-label consumer. | Payload containment and forward preservation hold. A group bijection, payload equality, or reverse owner implication would be stronger and is correctly excluded. |
| Singleton selection | `Branches.lean:105–118` requires distinct origins in the unique-color case. At 203–205 the mixed case concludes `∃ v g, (g = a ∨ g = b)` with a singleton condition. | The report preserves the existential alternative. It does not claim that both attempted candidates preserve the same target partition. |
| Exact erase and suppression | `EraseLift.lean:40–87,163–180` uses actual nonroot selected membership and distinct origins; the owner exclusion additionally uses the singleton. `Suppression.lean:142–144,191–233` maps new paths into old paths and constructs terminal-hull supports. | Exact surviving group records and owner transport hold on display graphs. A new display edge need not be one old edge. |
| Exact attempt | `CutRecords.lean:166–180` explicitly takes `Nodup`, `RootZeroOnly`, `CutsAvoid`, a monochromatic source partition and selected nonroot singleton. At 181–186 it derives all guards and unfolds `attempt`. `SourceAttempt` at 190–202 is a conclusion. | The continuation `f` is arbitrary. The local invocation does not certify its returned output. |
| General and initial consumers | `CutRecords.lean:209–219` takes the local origin invariants and concludes a finish equality or existence of a selected singleton together with `SourceAttempt`. At 220–236 it derives the normalized partition and chooser premises. At 240–257 it initializes the invariants from `fromTree`, the Boolean checks and block monochromaticity. | The report correctly distinguishes general explicit premises from the initialized state. Valid original identifiers additionally use the sublist premise of `Origins.lean:113–136`. |
| Cut names, output syntax and work | `CoreInvariants.lean:61–62,118–127,166–173` proves distinct nonroot recorded names and a list-length equality. `CoreProgram.lean:230–237` bounds prefix/attempt counters and explicitly leaves per-node work and reconstruction open. | The report does not promote identifiers or counts to original components, realized cut costs, or total operation work. |

`SourcePartition` has actual, terminal-exact, connected and disjoint fields
(`CoreGraph.lean:189–195`). It has no component-realization or finite-block-count
field. The report's local interpretation therefore matters: no step in the
inspected chain supplies the original residual-component relation merely by
constructing this structure.

The frozen missing assertion remains explicit. `FIRST-GAP.md:24–48` requires
reachability-derived original residual components, an exact leaf-bearing split,
unchanged detached components and finish-output identification. Its lines
52–60 separately retain finite-budget coverage, realized cost, raw mass and
polynomial implementation work. The report and trace preserve these limits.

## Counts and provenance

These are **retrieved execution results**, not executions performed in this
framing review. The units in `VERDICT.md` agree with their named records.

| Reported quantity | Record opened | Assessment |
|---|---|---|
| 72 author immutable files and 26 preserved readiness files | `CANDIDATE-PIN.json`, candidate-pin log, `EVIDENCE.json:2–3` | Retrieved identity/preservation results; no second full integrity audit claimed here. |
| 49 clean controls and 49 deliberately false expected twins | `PRE-CANDIDATE-RECEIPT.json`; `algorithm-integration-fresh-review-controls-v1.json`, fields `declared_controls`, `clean_passed`, `false_expectations_caught` | Pre-candidate instrument controls. They remain distinct from Lean false-proposition diagnostics. |
| 18 positive source modules | Source-replay receipt `positive_modules` and `rows`; `EVIDENCE.json:7` | The negative `FalseControls` module is separate. An isolated directory containing 19 candidate modules does not imply 19 positive modules. |
| 1,415 module-origin declarations; 144 private; 966 beyond 449 explicit source declarations | `AXIOM-INVENTORY.json`, metadata `total_originating_declarations`, `private_declarations`, `additional_to_author_explicit_inventory`, `author449_comparison` | The inventory reports defining-module enumeration, including generated/private names, and no axiom violations. The 449 comparison rows report matching axiom sets. These are audit units, not new mathematical results. |
| 76 finite assertions from 30 frozen controls | `COMPARISON-MAP.json`, `assertions`, `controls_with_compiled_fields`, `mapping`, `unsupported_fields`; comparisons-v1 receipt | The report explicitly retains unsupported fields for the original graph controls and source reading. It does not imply that all 49 controls have a candidate decidable API. |
| Six explicit falsity diagnostics | `FalseControls.fresh.log` (three), `FreshComparisonsFalse.fresh.log` (two), `KernelExplicitFalseV3.fresh.log` (one) | Each opened log contains the explicit `decide` proposition-falsity diagnostic. The decomposition is 3 + 2 + 1. |
| Custom axiom/private dependency caught; clean twin passed | `KernelCustomAuditV3.fresh.log`, `KernelCleanAuditV3.fresh.log`; origin-audit-v3 receipt `rejected_custom_entries`, `clean_entries` | The custom log includes the axiom, public theorem and `_private...privateLeak`, all depending on `AuditPlant.hiddenBad`. The clean row has no axioms. |
| Generic broken-import failure excluded | `KernelBrokenImportV3.fresh.log`; origin-audit-v3 receipt `generic_import_refusal_not_counted_as_falsity` | The log contains an unknown-module diagnostic and no proposition-falsity diagnostic. Its nonzero exit does not enter the six. |
| Two corrected audit-adapter versions and one corrected scope adapter | `ADAPTER-FAILURES.json`; v1/v2 driver logs and `KernelCleanAudit*.fresh.log`; `ScopeWitnesses.fresh.log` | Four retained audit source/log pairs record import compatibility failures; the scope pair records the missing `RootZeroOnly` unfolding for Decidable synthesis. The report correctly attributes these failures to review adapters. |
| Five source-model witnesses and six subsequent actual-code scope cases | Hostile-semantics JSON; scope-witnesses-v2 receipt and `ScopeWitnessesV2.lean` | Both are post-contact source-scope evidence. The report correctly excludes another replication and labels the fabricated-origin state unreachable. |

The contact ledger records four newly read specifications/dependencies,
prior geometry knowledge and filename-only pre-freeze exposure. The report
preserves those contacts. Neither independent authorship of an adapter nor a
second invocation of Lean supplies a disjoint mathematical model. The present
report makes no such independence claim.

## Audience objections

The audiences include the communities whose source mathematics and proof
machinery are used, the incumbent algorithm community, practitioners who would
consume the interfaces, and a general reader who might read only the opening.
The novelty objections below test the report's scope. No literature novelty
review was performed and no priority or performance advantage is accepted.

| Audience | Axis | Strongest standard objection | Answer on the reading path | Severity / minimal correction |
|---|---|---|---|---|
| Lean/formal verification readers | Correctness | A structure with connected-support fields can hide the desired theorem in its inputs. Where are those fields and the attempt guards derived from the exact executable definitions? | The source/consumer table names the constructors, coarsening and exact attempt; the inspected consumers derive connectedness, quotient premises, selected membership and guards. `SourceAttempt` is constructed. | None. Preserve the explicit premises. |
| Lean/formal verification readers | Novelty | Why should generated declarations, another compiler run or another audit adapter count as a new theorem or independent proof? | The opening identifies the same reviewer lineage and zero replications; the evidence section calls diagnostics check units. | None. |
| Incumbent rooted-tree/graph algorithms readers | Correctness | A singleton in a suppressed display is insufficient to identify an original residual component, so where is the exact original-edge split theorem? | The opening retains residual components OPEN; the final obligation specifies the live original edge, exact split and detached components. `FIRST-GAP.md:24–48` is precise. | None. |
| Incumbent rooted-tree/graph algorithms readers | Novelty | What advance over existing algorithms, or smaller recurrence base, has actually been established? | The opening accepts no smaller base or novelty claim and keeps all milestones OPEN. Local integration is the accepted object. | None; no prior-art conclusion follows from this source-only review. |
| Generator implementers and interface consumers | Correctness | A target-preserving branch under arbitrary continuation does not ensure a budgeted output, wrapper acceptance or polynomial work. What can callers actually rely on? | The opening retains budgeted coverage and work OPEN. The exact-attempt row names origin invariants; the duplicate-label paragraph separates raw checks from `generate`; the budget-zero witness and final obligations exclude output inference. | None. |
| Generator implementers and interface consumers | Novelty | Does the interface establish a usable complete source generator or improved runtime? | The opening expressly leaves the generator and base unaccepted; the source/count rows limit the result to local operations and syntactic counters. | None. |
| Verification-methodology and reproducibility readers | Correctness | Did a failed import get counted as a false theorem, or were candidate controls changed after a detector failed? | The evidence section separates explicit falsity, custom-axiom detection and import failure, retains the unsuccessful adapter versions, and states no candidate source/frozen expectation changed. The opened logs agree. | None. |
| Verification-methodology and reproducibility readers | Novelty | Are post-contact witnesses being promoted into blind controls or extra independent replications? | The opening, semantic-witness section and scope records disclose lineage and source-derived mathematics; the five model cases and six actual-code cases are separate from pre-candidate controls. | None. |
| General mathematical reader | Correctness | Does “confirmed” mean that the complete algorithm is verified? Can the cited source files be found directly? | The opening defines the scoped confirmation and immediately retains the full obligations OPEN. The revised source-locator introduction and trace name the exact roots. | LOW L1 resolved by naming the source roots. |
| General mathematical reader | Novelty | Does the scale of declaration/control counts imply scientific progress or another replication? | The evidence section explicitly calls them check units, and the opening rejects a novelty claim. The revised closing paragraph identifies the excluded X0 graph census. | LOW L2 resolved by identifying the census. |

## Minimal corrections

| ID | Location | Rule | Proposed correction | Applied here |
|---|---|---|---|---|
| L1 | `VERDICT.md`, source-locator introduction; `CONSUMER-TRACE.json`, `source_locator_base` | reading-contract locator precision | Name `research/rmaf/algorithm/universal233/integration/`, the manifest-listed core root and `research/rmaf/lean/RMAF.lean`. The basenames then have an unambiguous local address. | Yes, by the report owner; the final diff was read and verified. |
| L2 | `VERDICT.md`, last paragraph | prose-lint F4 internal consistency | Specify the excluded X0 graph census, so readers do not mistake “broad census” for the declaration inventory just described. | Yes, by the report owner; the final diff was read and verified. |

No source, expectation, new result or wider hedge is needed. The remaining
scientific obligations are the report's stated open obligations.

The final trace also moves the four OPEN rows' future requirements from
`exact_hypotheses` into `unproved_consumer_requirements`. I verified the diff:
the requirement strings and the confirmed theorem hypotheses are unchanged.
This correction distinguishes an unproved future consumer from a theorem
delivered under premises. Original reviewed drafts are preserved as
`VERDICT-draft-v1.md` and `CONSUMER-TRACE-draft-v1.json`.

## Standalone opening read

After the evidence and source review, I reread `VERDICT.md:1–17` separately,
using only that passage to judge its headline. It says the accepted object is
the delivered local interfaces at their printed hypotheses; it keeps original
residual components, finite-budget coverage, cost/mass/work, all three
milestones and novelty open. It discloses same-lineage review, zero additional
replications and contacted dependencies. An opening-only reader has no basis
for treating this report as verification of a complete 2.33 algorithm.

I also read the report sentence by sentence for parse/antecedent defects,
importance inflation, provenance drift, number units and repeated status
language. The repeated local/open qualifiers each protect a separate consumer
claim; trimming them would weaken scope precision. The two LOW corrections
above concern navigation and terminology. No additional prose correction was
identified. No HTML comments occur in the report; PDF rendering does not apply
to this Markdown review.

## Review identity

Initial reviewed `VERDICT.md` SHA-256:
`39c13533381dd98f4bb9bbfec94c1c383954cad9f51af7629950a5e799c79220`.
Initial reviewed `CONSUMER-TRACE.json` SHA-256:
`329f81a9739b29392b62fff5809a95bb6df7266bd2e2219f347b4e71b0168175`.
The initial hashes identify the preserved drafts. After the owner completed
the wording and trace-schema corrections, I read the full diffs and reread
the unchanged opening separately. Final current `VERDICT.md` SHA-256:
`75786d256533a305f57720b09b3c5b7427748299df5a9b5a1642b23897ceb3b0`.
Final current `CONSUMER-TRACE.json` SHA-256:
`27a39a9401f701bb643799908b4ec25f7eb042054f4404cb32f7faffad28a9bd`.
These final hashes were measured with `shasum -a 256` after the reported
corrections. Hashing files and reading retained receipts are distinct from
fresh execution of the scientific checks reported in those receipts.
