# Review2 evidence

This one-shot review independently reconstructs the restricted normalization and local 2B exchange. It is not a general AF toolkit. The toolkit index has no equivalent rooted cut/yield verifier, and this task required an evaluator independent of author and previous-reviewer code.

- What it does: `fresh_graph.py` explicitly cuts and contracts rooted graphs, retains edge-path provenance, and compares yielded forests. AF membership is tested by exhaustive F1 cut-yield enumeration.
- When to use it: replay the small fixtures and bounded local families in this review. Exhaustive enumeration grows exponentially; do not use the same family sizes as a runtime claim for arbitrary forests.
- Output meaning: exact sets, original IDs/endpoints, canonical labelled topology and actual denominators. An assertion failure is a failed check; no-fire counts are finite evidence only. Elapsed seconds are measured wall time and have no scientific-acceptance meaning.
- Trust conditions: known-answer controls and deliberately wrong topology/edge claims run before target fixtures, plus the independently read primary conventions. Author/reviewer evaluator code is neither imported nor read. The Lean checks establish only each actual statement.

Replay from the workspace root:

```sh
./bootloops-python research/rmaf/thesis_correctness/repair/review2/fresh_graph.py controls
./bootloops-python research/rmaf/thesis_correctness/repair/review2/fresh_graph.py frozen
./bootloops-python research/rmaf/thesis_correctness/repair/review2/fresh_graph.py boundaries
./bootloops-python research/rmaf/thesis_correctness/repair/review2/fresh_graph.py geometry
./bootloops-python research/rmaf/thesis_correctness/repair/review2/local_hunt.py
./bootloops-python research/rmaf/thesis_correctness/repair/review2/local_hunt.py pendants
./bootloops-python research/rmaf/thesis_correctness/repair/review2/consumers.py
./bootloops-python research/rmaf/thesis_correctness/repair/review2/rebuild_lean.py
./bootloops-python research/rmaf/thesis_correctness/repair/review2/rebuild_v2.py
```

The first three commands were executed before proof reports were read. The first full geometry run also preceded the proof reads. The explicit final surviving-node/edge-map equality assertions were added later and rerun; topology, unchanged-edge transport, root fragments, and exact cut counts had already been checked independently. No initial-code hash was recorded before proof reading, so the chronological record consists of the workfile, tool calls and retained run logs; final file hashes are supplied for replay integrity. This limitation is not replaced with a retrospectively invented freeze.

`REPORT.md` states the reviewed theorem and consumer scope. `INDEPENDENT-DERIVATION.md` preserves the before-proof corridor reconstruction. JSON receipts retain all actual quantities; `verdict.json` is the delivery summary and `bugs.json` contains the executed broader-statement failures. `source-ledger.json` records source pages and exact extraction strings. `lean-build/` and `lean-v2/` contain unchanged local source copies, build logs, output objects and additional axiom prints. None changes the originals or aggregate counts.
