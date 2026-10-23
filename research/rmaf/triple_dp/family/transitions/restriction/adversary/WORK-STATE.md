# Independent restriction adversary

Target read first on 2026-10-14. Construction/evaluation has not begun.
Scope: independent graph and partition validator; live restriction and reconstruction evaluator; frozen control gate; measured bounded hostile enumeration.
No author checker imports or reads. All failed attempt bytes and logs retained.
State: skeleton created; reading frozen inputs and applicable protocols next.

## Protocol and lineage record

2026-10-14: Read the frozen controls and preconstruction pins, restriction README/WORK, prove-protocol, planted-truth, independence-bookkeeping, timing-discipline, tool-stewardship and acceptance-gate. Shared semantics read directly in FamilyAssembly.lean (Family, Vertex, LeafAt, cost), FamilyModel.lean (address/leaf distinction), ConnectedRegions.lean (OnPath and PathConvex). No author evaluator, merge implementation, other adversary, or fresh checker source was read or imported.

The toolkit index and emitall GUIDE were consulted: emitall checks recorded claim emissions but does not construct tree-address families or independently validate restrictions, so this problem-specific one-shot exact graph evaluator is justified. It will not be promoted to a general toolkit instrument.

The frozen fixtures are seen calibration data, not an unseen theorem certificate. This independent arm shares the target, fixtures, and Lean definitions with the author; its executable logic is fresh. Shared spec transcription is an acknowledged remaining risk. Exact integer/set arithmetic has no floating precision parameter. Bounded NO-FIRE will not be called a proof.

## Preregistered search and failure rule

After all frozen controls and the numeric-blind-copy outer gate pass, measure the exact evaluator on controls, then run a tiny pilot over all two/three-leaf binary shapes and a bounded exhaustive search over all four-leaf binary shapes. Repeated leaf values are used. Enumerate partitions of leaf addresses and all assignments of internal vertices to an index or unused, thereby admitting nonminimal dangling incursions. Validate input families before evaluation. Preserve each in-regime mismatch as an exact witness and stop on FIRE. The progress unit is the completed candidate/family evaluation, retained in JSON receipts. All construction, count, exact support recovery, index bijection and four-transition cost equations are attacked. No large census.

## Executed frozen controls and measured pilot

Original frozen control run: PASS, 8/8 positives, 4/4 malformed rejected, 5/5 wrong numbers caught and clean twins accepted, 3/3 support corruptions caught and clean twins accepted, 1/1 outside-premise control classified correctly. Original execution took 0.001718 seconds, excluding wrapper startup. The numeric-blind copy returned FAIL with exactly the five wrong-number failures: all five wrong numbers escaped it, all five clean twins passed, and the outer control gate rejected that checker. All five outer-gate criteria passed. Original/copy bytes and failure receipt remain retained.

Pilot (same evaluator, all two/three-leaf shapes, all repeated labels): 99 candidates, 34 valid families, 32 in regime, 2 outside premise; no property failure. Total evaluator time 0.002707208 seconds. In-regime cases included 23 closed-parent child-root owners and 11 unused-internal cases. All four transition types appeared (9 closeBoth, 8 extendLeft, 8 extendRight, 7 merge).

Before four-leaf launch: exact candidate count is 5 * (2^3 + 7*3^3 + 6*4^3 + 5^3) = 3530 (five shapes, Stirling leaf partitions and three internal assignments). Straight pilot-throughput projection is 3530/99 * 0.002707208 = approximately 0.097 seconds; this is only a floor because graph/path work increases with vertices. An explicit 15-second wall cap bounds this tiny test; no long run is authorized or required. Progress is candidate/family counts in the resulting receipt. Complete all five shapes or report an incomplete cap, never round it up to a census.

## Four-leaf hostile search result

Verbatim script summary:

```json
{"elapsed_seconds": 0.04030400000192458, "stage": "hunt", "totals": {"candidates": 3530, "closed_parent_child_root": 181, "in_regime": 257, "outside_premise": 26, "repeated_labels": 257, "unused_internal_vertex": 110, "valid": 283}, "transition_counts": {"closeBoth": 76, "extendLeft": 64, "extendRight": 64, "merge": 53}, "verdict": "NO-FIRE-BOUNDED"}
```

Receipt: `research/rmaf/results/triple-family-transitions-restriction-adversary-hunt-v1.json`.
Control receipt: `research/rmaf/results/triple-family-transitions-restriction-adversary-controls-v1/outer-gate.json`.
Pilot receipt: `research/rmaf/results/triple-family-transitions-restriction-adversary-pilot-v1.json`.

Verdict: X0 NO-FIRE-BOUNDED. All selected finite cases satisfy exact child validity,
index enumeration/support, child-root ownership, occupied/live equivalence,
parent-index liveness, overlap characterization, block count, four-transition
cost, and reconstructed support/boundary/bijection/count/cost checks. The search
includes nonminimal supports through every internal assignment; convexity and the
open-branch premise are independently filtered. No counterexample or erratum was
produced. Universal restriction, normalization transport and Lean transition
recovery remain obligations for the prover and fresh reviewer.

No author construction code, merge implementation, or other checker was read.
The intentionally numeric-blind failure was the only failed execution. Its exact
bytes and stdout/stderr/JSON remain in place. No failed attempt was removed.
The original checker was never edited after pre-run pinning.
