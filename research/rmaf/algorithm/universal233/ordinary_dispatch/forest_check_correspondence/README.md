# Actual forest checker: qualified author result

Import `ActualInspection`, namespace `GenericForest.CheckCorrespondence`.
This release proves structural unit-operation upper evaluators with exact value
correspondence for the literal `ForestState.proper`, `sourceCheck`, `agrees`,
`GenericForest.accepted`, and `checked`. Full Boolean suffixes may be charged
when the production source short-circuits. Failed checks keep their cost.

The counterparts include repeated flattening inside every count closure,
label membership and duplicate scans, leaf-list materialization, restrictions,
four-way shape comparisons, original minimal-hull addresses, address equality,
source ownership/family filters, and length/subtraction/comparison slots.
For target/source/candidate bounds N, the checked counterpart costs at most
908*(N+1)^6. With `StatePayloadSize`, it is at most the actual frozen
`inspectionBill T ss q = 4096*(targetNodes T+sourceNodes ss+ss.length+q+1)^8`.
The proper-input guard is bounded even when malformed inputs are rejected.

`ReturnedPayloadBound` follows from proper ordinary callback soundness. It is
discharged for the sealed `FastOrdinary.solve` using `FastExact`: returned
forests partition the actual input labels, have nonempty blocks, and have at
most one total label cell and one block per target label. The label bit-cell
bound is conditional on the explicit input label-bit cap. Hostile callbacks
are retained: repeated payloads are rejected, their count traversal grows with
their actual size, and a symbolic family exceeds the frozen inspection sheet.

Actual candidate premises are derived before the parent acceptance scan:
initial source blocks from properness; singleton answers from the callback
premise; scheduler answers by direct recursion over literal jobs/run and the
pretest's actual returned forests; overlap candidates from the exact raw
filterMap and child solve soundness. Raw duplicate occurrences stay separate.
The general `raw_checks_bound` also applies to rejected bounded-size payloads.
No final acceptance result is used to bound a preceding callback's payload.

This is a source checker counterpart and unit-operation sheet result. It does
not prove native Lean machine cost. A Nat equality is still a unit scalar
slot; scalar provider bodies and a binary bit-cost lift are the next explicit
consumer. The imported old address/materialization meters retain their
original source-provider scope. No all-imported stored IR claim is made.
Functional algorithm acceptance, full runtime, base and novelty milestones
and independent acceptance remain OPEN. This is author development lineage.
