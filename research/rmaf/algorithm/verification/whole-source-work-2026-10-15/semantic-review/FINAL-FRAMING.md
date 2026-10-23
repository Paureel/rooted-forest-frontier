# Final framing pass

The four final artifacts preserve the intended scoped result. Two wording corrections listed below should be applied before sealing. No new scientific finding or verification result is introduced by this pass; no source, replay, control, inventory or earlier review outside the four requested final artifacts was read.

Read surfaces were `../RESULT.md` (32 lines), `../FINAL-RECEIPT.json` (213 lines), `../CONSUMER-TRACE.md` (29 lines) and `../COST-CORRESPONDENCE.md` (56 lines). Line locators below refer to those pre-correction versions. This child performed no computation or kernel replay, and adds zero independent replications.

## Corrections required before seal

| Location | Finding | Required correction |
|---|---|---|
| `CONSUMER-TRACE.md:8` | “scans A, then B, else C” may imply a third membership-list scan. The described code tests A and B, then defaults to the C callback. | State “scans A, then B when needed; otherwise evaluates the C callback”. No C membership validation guard should be implied. |
| `COST-CORRESPONDENCE.md:25` | The phrase “preregistered ... at most 8 operations per copied/mapped/reversed cell” obscures which contracts were pinned and which are explicit reviewed extensions. A prepend map creates two cells per selected address, whereas the table correctly allows sixteen operations per selected mapped item before the separate left-copy bill. | Separate the preregistered eight-per-copied-cell/address-bit contract from the reviewed ordinary map/reverse contracts. State that prepend mapping creates both an address cell and an outer list cell and receives sixteen operations per selected item in the local table. Do not describe every map/reverse allowance as a literal preregistered claim. |

These edits concern wording and provenance of the source contract. They require no expectation changes, new replay or alteration of the factor-64/cell-8 conditional envelope.

## Scope and consistency checks

| Concern | Final artifacts' treatment | Framing outcome |
|---|---|---|
| Fine-operation counterexample | `RESULT.md:3,13,18`, receipt claim `direct-outer-meter-as-fine-source-operations`, and `COST-CORRESPONDENCE.md:23` give the sixteen-cell, work-eighteen versus minimum-thirty-three witness. | The refutation targets direct unit identification. Each explicitly avoids claiming a counterexample to the author's full large total caps. |
| Corrected source envelope | `RESULT.md:14,18`, receipt `source_model` and `COST-CORRESPONDENCE.md:25–48` distinguish the corrected core F, conditional helper factor 64, outer multiplier eight, source inspection and separately checked arithmetic. | A formal extracted operational theorem is not claimed. The map/reverse contract wording needs the correction above. |
| Original imported source sharing | `COST-CORRESPONDENCE.md:12–14` identifies the parent's opened-definition inspection at original RMAF and Bridge sites. `:37` attributes the child's narrower block scrutiny and supplied constants accurately. | The child does not claim to have opened original RMAF/Bridge operational definitions or to have independently rederived their sharing. |
| Invalid-domain fallback | `RESULT.md:20`, receipt callback scope, `CONSUMER-TRACE.md:8–9,27`, and `COST-CORRESPONDENCE.md:11–17` separate total source fallback from semantic partition/support/occupancy premises. | No source refusal guard for overlap, missing parents or absent target labels is invented. The C-scan wording needs the correction above. |
| Typed adapter failure | `RESULT.md:28`, receipt `failed_adapters_retained`, `CONSUMER-TRACE.md:27` and `COST-CORRESPONDENCE.md:7` retain V1 elaboration failure and say V2 changes explicit types only, without expectation changes. | The failure is not counted as mathematical falsity or an accepted audit input. |
| Instrument execution | `RESULT.md:11,22`, receipt scheduling scope, `CONSUMER-TRACE.md:12–13`, and `COST-CORRESPONDENCE.md:21` distinguish original-source accounting from running both meter traversals or its unused refusal-tree field. | n/zero recorded callback counts are not presented as dynamic instrument traces. |
| Raw multiplicity and dedup size | `RESULT.md:22`, receipt target-span scope, `CONSUMER-TRACE.md:18,20` and `COST-CORRESPONDENCE.md:14–15` retain raw output duplicates and limit joint-signature dedup to target-selected leaves. | No quadratic scan of an exponentially large raw output list is hidden in the claimed form. |
| Selector/gate integration | The opening and table of `RESULT.md`, receipt OPEN claim, `CONSUMER-TRACE.md:21–22,29` and `COST-CORRESPONDENCE.md:54–56` state that supplied v is unbound to the selector result and no gate-count dispatch is implemented. | The claim concerns supplied-target components plus additive accounting; actual dispatch remains OPEN. |
| Bit and machine claims | `RESULT.md:16,22`, receipt machine obligation and `COST-CORRESPONDENCE.md:52` add scalar size/reference widths and keep representation/implementation assumptions explicit. | Compiler/GC/cycle verification is not inferred from source work or timing. |
| Complete algorithm and novelty | All four artifacts retain all three milestones OPEN. `RESULT.md:30–32`, receipt final fields and `COST-CORRESPONDENCE.md:56` list missing transitions/history/budgets/invariants/termination/reconstruction/coverage and disclaim novelty. | Strict rational margin is not promoted to a full faster-algorithm theorem. |
| Replication provenance | `RESULT.md:32`, receipt `independent_replications_added:0`, and `COST-CORRESPONDENCE.md:37` disclose the same reviewer lineage, reused core ledger, one bounded semantic child and parent-supplied constants. | No additional independent replication is claimed. |

The final opening carries the cost-contract correction, direct unit refutation, dispatch limitation and OPEN milestones before the quantitative evidence. The final receipt's claim types match the prose. This pass found no further required scope or attribution correction in the four requested artifacts. Seal should follow only after the two wording corrections are applied and checked by the parent.
