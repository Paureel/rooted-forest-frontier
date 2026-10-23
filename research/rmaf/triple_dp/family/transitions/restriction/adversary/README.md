# Independent restriction X0 evaluator

This is a problem-specific, one-shot exact falsifier of the pinned live-child
restriction target. It builds the address graph afresh, computes unique paths by
breadth-first search, checks every Family field, restricts to indices with leaves
in each child, and reconstructs closeBoth/extendLeft/extendRight/merge with explicit
fresh constructor indices and a checked bijection to the parent indices. Leaf
values never identify vertices or regions.

Use it to replay this X0 battery or the recorded tiny search. It does not check
Lean proof terms, executable refinement, normalization premise transport, or a
universal statement. Those require the main proof and a separate fresh review.
The neighboring emitall package checks quoted receipt values; it does not provide
this graph/family evaluator.

The `controls` command produces exact integer/set results. PASS means all frozen
expected fields and clean/corrupt pairs were checked at their declared
nonzero denominators. The numeric-blind copy is intentionally invalid: its FAIL
receipt is the expected evidence that the outer control gate works. Hunt verdict
NO-FIRE-BOUNDED means no mismatch in the explicitly enumerated finite domain,
never universal validity. FIRE-CANDIDATE preserves the exact input and output and
requires an independent replay before a certified target erratum. A time cap is
INCOMPLETE and cannot be relabeled NO-FIRE.

All code, frozen target/control bytes, and shared semantic sources are pinned in
PRE-RUN-PINS-v1.json before the first evaluation. The original control gate must
pass before search; the mutant must let all five wrong-number controls escape and
must be rejected by the outer gate. The frozen expected answers are calibration
inputs seen before authoring, so they are not an unseen final theorem certificate.
A fresh checker must reimplement from the shared spec without importing this code.

Replay from the workspace root, using a fresh output name each time:

```
./bootloops-python research/rmaf/triple_dp/family/transitions/restriction/adversary/run_gate_v1.py --outdir research/rmaf/results/triple-family-transitions-restriction-adversary-controls-REPLAY
./bootloops-python research/rmaf/triple_dp/family/transitions/restriction/adversary/exact_restriction_v1.py hunt --gate research/rmaf/results/triple-family-transitions-restriction-adversary-controls-REPLAY/outer-gate.json --min-leaves 2 --max-leaves 4 --cap-seconds 15 --out research/rmaf/results/triple-family-transitions-restriction-adversary-hunt-REPLAY.json
```

Change record, 2026-10-14: v1 authored independently from the pinned target,
frozen fixtures, and direct Family/PathConvex definitions. No prior author checker,
merge implementation, adversary, or fresh checker source was read or reused.
There were no corrective code revisions after controls; the intentionally
numeric-blind copy and its failure logs are retained. No general toolkit interface
was changed. This README is the local instrument index entry.
