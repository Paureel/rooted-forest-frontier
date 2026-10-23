# Final audit resource policy v1

Pinned before final instrument implementation. Preserve every prior record.
Parent reports low disk capacity and a prior review failure from ENOSPC.
New final replay uses per-module source builds and per-module producer audits.
Each process has a 30-second pilot cap. Every producer stdout byte is streamed
to gzip; no complete all-module raw producer dump is retained. Per-module raw
output cap: 64 MiB; individual line cap: 16 MiB; aggregate compressed-output
and source/build directory cap: 256 MiB. Require at least 2 GiB free before
each new process; stop and retain the exact incomplete scope if exceeded.

The source producer generator is the completed author detector. Fresh Std
controls run before any scientific audit: clean shared name/type twins in
both import orders, custom axiom with same name/type and own clean theorem
in both orders, private/unused axioms, known true/false, missing/duplicate
rows, wrong source module path, original/adapted source-byte corruptions.
New streaming parsing is tested by those same fixtures before source audits.

This is author development. All main algorithm milestones and novelty OPEN.
