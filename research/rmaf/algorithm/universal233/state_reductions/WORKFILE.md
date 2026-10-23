# Actual forest-state reductions workfile

Target: TARGET-v1.md. Status: OPEN; this author may deliver CLOSED-UNVERIFIED subinterfaces only. All three main solver milestones remain OPEN. Fresh nonauthor acceptance is separate.

## Scope and dependencies
Use only completed dependencies named in TARGET-v1.md. No pair_assembly, kept_parent, reviews, active candidates, or children.

## Tool choice
The BootLoops tools index has no rooted-forest theorem prover. Reuse the original RMAF Lean model and completed restriction bridge; a problem-local source-bound wrapper is necessary for finite forest states and their controls. Runtime is initially unknown; measure small controls before larger runs.

## Controls pre-registration
Pending: explicit pin and executable original-Boolean true/false fixtures before any theorem construction.

## State model
Pending: literal partition, embedding, source-component and restriction checks; no assumed transport fields.

## Singleton cleanup
Pending: forward/reverse transport, exact additional cost, reconstruction, strict label decrease.

## Synchronized cherry
Pending: no-larger replacement, literal contraction/expansion, exact cost and strict label decrease.

## Proof receipts and first open consumer
Pending.

## Integrity and acceptance
Pending source pins, isolated compile, standard axioms/full origins, false and corruption controls. No VERIFIED-CLOSED claim by the author.

## Executed controls and first partial interfaces

The pre-proof receipt is build/preproof-controls-receipt.json; Controls compiled and all four FalseControls assertions failed with `is false` before Singleton.lean was written. Differing-address cherry and unary-suppression fixtures used arbitrary labels 17,31,47,89.

Singleton.lean has now compiled: `singleton_forced` proves [a] is present exactly once and every block containing a equals [a], directly from proper original checks and refinement. `singleton_additional_cost` proves the exact |F|-|ss| equality for the executable erase transformations. Initial failed builds are retained as Singleton-first.log; corrected build is Singleton-second.log. These are author kernel evidence, not fresh acceptance.

## Singleton cleanup proof

The forward theorem `Forward.singleton_cleanup_forward` has compiled. Its target embeddings use the completed `RestrictionBridge.pairwise_transport`; source families remain exactly equal because each other source omits a. The reverse theorem `Reverse.singleton_cleanup_reverse` reconstructs [a]::G and checks original validity. `LeafClear.singleton_clear` proves a singleton leaf embedding is clear of every block omitting a, through both rooted-span/minimal and minimal/minimal checks. The cost theorem for reconstruction and `singleton_decision_equivalence` have compiled. The latter preserves the same arbitrary Nat budget q. `singleton_strict_decrease` proves label count decreases exactly by one, including the none boundary.

`Singleton.initial_state_agreement_iff` additionally proves that on a proper [S] initial state the new literal checks are equivalent to original RMAF.agreement.

## Cherry partial proofs

`CherryGraph.actual_separated_cherry_singleton` has compiled against actual state agreement: two separate endpoint blocks force one endpoint singleton. The proof derives the actual cherry-parent address from the executable cherry test, puts it in both minimal embeddings if both endpoint blocks have extra labels, and contradicts original pairwiseEmbeddings.

`CherryTopology.synchronized_endpoint_reassignment_topology` has compiled. Adding b to a block containing a and omitting b preserves literal restrictionAgrees when both actual trees have the cherry. The two addresses are quantified independently; sibling swapping uses ordinary label-preserving RootedIso. No coarsening or transport premise is stored in State.

The first missing graph consumer is printed verbatim in OPEN-CONSUMER-v1.md. Full cherry replacement, contraction/expansion validity and decision equivalence remain open.

## Replay history

The first isolated replay compiled all proof modules, then rejected a missing-origin inventory because Consumers contained only anonymous examples. The named consumer declarations correct that inventory issue. The failed result directory and log remain preserved. A second full isolated replay passed, auditing 531 declarations before the initial-state equivalence was added. A third replay includes that extra theorem; its final certificate is the record of current sources.

The supplied `./bootloops-check emitall` suite passed (one package). Other toolkit suites do not test these rooted-tree proofs and were not run by this arm. No external numeric engine was required. All Lean proof builds use bootloops-lean, an isolated LEAN_PATH, and a local lean-toolchain copied from the permitted integration checkpoint.

## Independence and review

The control answers were constructed before universal proof development. The proof author ran the controls and replay; this supplies kernel evidence but no fresh nonauthor acceptance. The parent may assign fresh review separately. No children were launched. The outward-facing referee-sim fresh-context requirement is not claimed satisfied by these internal notes; no public scientific or novelty claim is made.

## Current final author receipt

The third isolated replay passed. Verbatim summary fields from replay-third.log:

```
"status": "PASS_AUTHOR_KERNEL_REPLAY_PARTIAL_TARGET",
"singleton_cleanup": "CLOSED_UNVERIFIED",
"common_cherry": "OPEN",
"module_origin_total": 537,
"receipt": "results/algorithm-universal233-state-20261015T094847Z"
```

The proof inventory covers 14 source modules; all imported source modules resolve to this isolated result directory, and other dependencies resolve to the local Lean runtime. The observed axiom union contains only propext, Quot.sound, Classical.choice. Four pinned false mathematical assertions and the arithmetic twin were rejected. Missing-record/path/origin corruptions, hidden custom axiom, and changed source bytes were caught. The positive controls contain 24 assertions and Consumers contains seven named applied checks. RESULT.md states the current scope; OPEN-CONSUMER-v1.md states the first missing graph assertion.
