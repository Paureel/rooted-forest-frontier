# Recovery source ranges and concrete finite-bit primitives

Author result: source-local recovery ranges and named finite-bit/copy implementations are proved. The complete recovery finite-bit execution lift remains open at persistent represented initialization. Import `RSCopyBounds` from the canonical receipt identified by FINAL-MANIFEST-v1.json, with the exact import order in IMPORT-COMPATIBILITY-v1.json.

For original recovery source tree S, put N=inputResource S. The source proof gives N≤(treeNodes S+2)^2. Given original labels below 2^L and actual checked partition P, final block colors are block heads or zero and remain below 2^L. Normalization, successful erasure and every recursive callback preserve these values; selected groups also obey the source footprint cap. The callback relation admits extra guard-failing states, so it covers actual callbacks without using acceptance or successful recovery as a resource premise.

StateCap carries footprint+detached.length+cuts.length+2*q≤N, bounded detached label/address lengths, and bounded source cut address lengths. TreeAddresses bounds all internal node addresses. OutputCap gives at most N+1 blocks, at most N labels per block, flattened output length≤N*(N+1), at most N cut addresses, and original label/address caps. The proofs apply to every returned output of every prefix, not just the head selected by recovery.

Let eventSize be outputs.length+refusals.length+visited+childAttempts+pruned. The actual run satisfies eventSize+3≤8*2^(q+1). Thus every receipt scalar/list count is below 2^(Q+5) whenever q≤Q. Initial q is exactly min budget (leaves.length-1). scalarWidth N L Q=L+2*labelBits(N+1)+Q+8 proves the stated input, label, receipt and flattened-output width inequalities. These are mathematical width certificates, not runtime Nat conversions.

Concrete algorithms act on supplied LSB-first Bool lists: equality, order, saturated subtraction, copied minimum, fixed-width counter addition/increment, list length, clipped budget and literal block-color scans. Value and work theorems name their actual bodies. The primitive family is bounded by 128*(W+1) under input array widths≤W; counter value theorems require nonoverflow. clipBudget costs≤160*(W+1)*(leaves.length+1); colorBits costs≤96*(W+1)*(flattened label count+block count+1).

Deep copy routines traverse each supplied bit and list cell. Under represented word widths W and the matching source footprint/output caps, a complete tree copy costs≤64*(W+4)*N and a complete output copy costs≤32*(W+4)*(N+1)^2. These bounds pay those copy invocations. They do not count copies made by a represented run that has not been implemented.

The prior actual source envelope remains 64*(BudgetOptimization.recoveryEnvelope n+32)*2^q. Its exactly-once 233/100 absorption remains the prior source theorem. No new whole-recovery bit coefficient is asserted. See FIRST-GAP-v1.md for the exact missing producer and BOUNDARY-v1.md for permitted use.

Thirteen owned modules, 712 stored occurrences, 17 known literal checks and 12 deliberately false claims were audited. Hash, missing/duplicate producer and custom-axiom corruptions were caught. Both audits and all compilation/control failures are retained. The author/compiler/library lineage is shared; independent acceptance credit is zero. Native/compiler/IR and the full 2.33 runtime remain open.
