# Rule5 admitted and classifier source stage

The actual `Rule5FinalClassification.selectFinal` body now has an executable
value companion and a concrete polynomial structural-work bound. The value
companion includes the literal admitted predicate with its strict
`let P := pendantPartition S a b`, the large/size-two/outside scans, the bad
source scan, and the boundary classifier. Whole Rule5 local work remains open
at the selected-branch materialization and execution in `AdmittedHandler.lean:14-27`.

`FinalClassifierWork.lean:114-130` proves `final_value` without a proper-input
premise. `:149-174` defines `finalBudget` and proves `final_work`. With
`nt = (leaves T).length`, `ns = (leaves S).length`, source labels below `2^L`,
and the named checker fee at most `K` on `CheckDomain (nt+ns) L`, the bound is

    (finalMeter fee T S a b).work ≤ finalBudget nt ns K.

All component budgets are explicit natural-number polynomials in the source.
The source proof assumes no whole-classifier cost premise. Checker requests
are exactly `.embedding T P` and `.restriction T S B`; `final_calls` proves
that every recorded request has the stated size and label domain.
`final_call_count` bounds their number by `7*ns+3+(2*ns)*(2*ns)`.

The meters retain failed and duplicate scan occurrences. They charge the two
minimal-embedding evaluations in each incident predicate, the two outside
checks in the boundary selector, each core-label construction in the outside
predicate, and the inner cut-list construction for every outer bad-source
candidate. Filter and filterMap scans finish before their literal `head?`
selection. `ClassifierPayload.final_payload` derives the stored source label
and original-address bounds from the actual selection.

The canonical replay compiled 22 owned modules and audited 980 stored
declaration occurrences. The count measures audit coverage only. The audit
retained non-theorem and opaque bodies, traversed full theorem references,
and found only `Classical.choice`, `Quot.sound`, and `propext` in the axiom
union. The compressed producer logs contain the exact stored expressions;
`producer-occurrences.json.gz` records their hashes and reference closures.

The replay checked the previous pendant controls and all 19 new classifier
controls. Lean rejected four deliberately false claims about zero incident
work, a changed boundary result, omitted duplicate work, and zero final work.
Fresh audit controls rejected direct, private, unused, and dependency custom
axioms, missing/duplicate producer rows, foreign object paths, changed source
and object hashes, and changed generated audit bytes. Two clean producer
orders and two opaque bodies passed. These checks use the author's source,
Lean runtime, and the earlier audit-template lineage; independent
reconstruction and adversarial acceptance remain open.

An initial negative-control launch refused below the 3 GiB disk floor before
starting Lean. `RESOURCE-REFUSAL-v1.md` retains the refusal and the subsequent
free-space measurement. The bounded retry and the canonical replay both ran
through the same disk guard. Every compiler process used a 30-second limit
and `-M3072`; the canonical result directory used 44,090,566 logical bytes at
its final resource check.

The current target requires preserving writable source modes and inodes via
read-only exact snapshots. The canonical replay therefore copied dependency
and owned source/object bytes into read-only snapshots and recompiled only
owned sources. Five prefix dependency source/object pairs were writable at
their original paths; no chmod or write touched those originals. Snapshot
hash equality establishes identity, not independent replication. The replay
verified that every owned original source retained its hash, mode, and inode.
The earlier common and prefix manifests remain unchanged.

The structural work unit still needs a separately justified scalar/cell
correspondence, and the checker fee remains conditional on its explicit
bounded domain. The multiplication theorem `final_scaled_work` introduces
no compiler, native-runtime, machine-word, or bit-semantics claim. No global
recurrence, binary-cost integration, improved-base acceptance, novelty claim,
or full 2.33 acceptance is asserted here.
