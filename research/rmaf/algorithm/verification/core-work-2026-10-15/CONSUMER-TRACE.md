# Frozen core-work consumer trace

This trace covers only the manifest-bound standalone source generator. Source paths below are immutable copies under `isolated/`; `CANDIDATE-PIN.json` supplies their exact originating paths/hashes. The source-cost bridge is COST-CORRESPONDENCE.md; successful Lean value projection alone is insufficient.

| exported assertion / source | premises actually supplied | result and scope |
|---|---|---|
| Work.meterGenerate_receipt:415 | any Tree, color:Nat→Nat, budget:Nat; unfolds the actual Nodup guard, min cap and conversion | Exact Receipt equality with frozen CoreProgram.generate. No cost conclusion follows merely from equality. |
| Work.meterGenerate_calls:422 | same; initial check before conversion at CoreProgram:124 | n syntactic source color calls on Nodup success; zero on refusal. Arbitrary evaluation cost external. |
| Work.normalize_footprint:19; erase_footprint:33 | arbitrary GTree; successful literal erase equation for erase | Current constructor/label/address footprint cannot increase. Colors and scalar encodings excluded from footprint. |
| Work.fromTree_footprint:88; treeNodes_le_twice_leaves:82 | any Tree and prefix address | Initial footprint ≤N(|p|+N+2); N+1=2n. Source conversion uses p=[]; current footprint ≤N(N+2). |
| Payload.selected_mem:12 | literal choice .one or either .two group | Chosen group actually occurs in current groups, so group_size supplies address/label bounds. No arbitrary chosen-group input is silently substituted. |
| Payload.Prefix:28; prefix_sizes:35 | induction from initial state through actual selection, root/duplicate guards and successful erase | At depth d: current footprint≤S; d detached/cut records; detached volume≤dS; each stored address≤S. Actual run calls have d≤B by recursion; attempted final children d≤B+1, even if immediately pruned. This is syntactic stored state, not residual graph components. |
| Work.Within:246; continuation_within:256; initial_within:428 | numeric resource, successful exact erase; initial cap B=min(q,n−1) | m=N(N+2)+N+1 is preserved for evaluated calls. This is not a simulation/cost hypothesis. Last overbudget local attempt is already charged in the parent. |
| Work.meterStep:138; meterRun:156 | actual normalize→choose; actual attempt guards/erase | Local charge occurs before finish/refuse/success or zero-budget pruning. Standalone meterAttempt refusal work=0 is not a standalone cost theorem; step's local charge pays it. |
| Work.meterRun_pruned:191 | actual run and its callback structure | Exact pruned continuation count, including two pruned children; local attempted work is still charged. |
| Work.appendCells:119; meterStep:149 | actual left Receipt | Counts outputs.length+refusals.length and copies once at each binary ancestor; exact cell-count comparison passes. Fine primitive operations need the explicit cell multiplier in the independent correspondence. |
| Work.run_records_events:219; run_records_bound:239 | literal returned receipt; no deduplication | Record count bounded through visited and childAttempts; includes refusals. Supports global materialized-copy recurrence, not a constant-time combine. |
| Work.meterRun_bound:296; envelope_closed:348 | Within m q and hand-assigned meter | Formal meter bound. Its unit-cell recurrence is not identified with exact fine source operations. Independent conservative recurrence bridges the displayed final formula under declared contracts. |
| Work.generate_work_bound:439 | any Tree/color/budget; supplied initial resource is proved internally | Formal bound on meterGenerate.measured.work, not an assumed callback cost. Independent inspection supplies actual source-operation coverage, initialization and multiplier. |
| Primitive.primitive_sheet_le_localCharge:165 | arithmetic on helper sheet | Kernel algebra only. Literal helper-as-fine-operation upper charge is refuted by groupsWork79 vs minimum86; corrected conservative sheet fits the final cap. |
| Controls:15–48 | fixed concrete fixtures | Twelve author positives recompiled. Fresh29 literal ledger cases compare values/calls/copies/prunes; finite evidence is not universal source coverage. |

The cost result supplies a standalone building block under ordinary q=k−1 and no implicit rho. The author package contains no implementation of the next ownership-prefix cost consumer. Its bound still requires actual finite-color construction/lookup costs and a weighted sum of capped generate costs over realized ownership prefixes, followed by actual pair/refinement/search/reconstruction composition below2.3391. Neither the numerical resource invariant nor geometry/source integration supplies this total.

OPEN-STATE-ORIGINAL and OPEN-CORE-REALIZATION remain open at original residual component correspondence. Finite-budget output coverage, whole weighted mass/work and the full faster solver remain open. All three main milestones remain OPEN. No novelty assessment is made.
