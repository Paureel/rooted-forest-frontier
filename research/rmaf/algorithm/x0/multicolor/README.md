# Multicolor X0 instrument

This one-shot instrument tests the pinned recursive multicolor source-cut
operations against an unchanged source-partition reference. The prototype
contracts homogeneous groups, detaches a group with a unique current color,
or branches on the two children of a mixed cherry. Each result includes the
original source edges, original label blocks, and contraction/deletion logs.

Use it to falsify the current multicolor core hypothesis before algorithm
construction. `prototype.py` imports no reference code and calls no optimum
oracle. The comparator uses the earlier X0 `fresh_oracle.py` to enumerate
every source-valid partition and check original vertex spans and cut graphs.
No target-tree agreement check is applied to an emitted source core.

For a nonempty source with r used colors, a result costs its actual number of
nonredundant source cuts, which must equal `pieces - 1`. Its mass at base c is
the sum of `c^(-cost)` over emitted cores. Coverage means each original valid
monochromatic partition refines at least one returned core. The empty source
is a separate null with zero cuts; its r=0 state is outside the mass hypothesis.
An empty core under an insufficient budget is a refusal only when no valid
partition fits that budget. An empty unbounded core is a failure.

The instrument must first pass its 19 controls, including the missed partition
from a deliberately omitted mixed branch and the nonempty clean twin. The
four-label exhaustive pilot precedes any five-label execution. Full original
receipts are immutable by the driver; the replay wrapper writes fresh names:

```sh
./bootloops-python research/rmaf/algorithm/x0/multicolor/replay_x0.py --stage controls --output research/rmaf/results/algorithm-x0-core-controls-replay-new.json
./bootloops-python research/rmaf/algorithm/x0/multicolor/replay_x0.py --stage pilot --output research/rmaf/results/algorithm-x0-core-pilot-replay-new.json.gz
./bootloops-python research/rmaf/algorithm/x0/multicolor/replay_x0.py --stage extension --pilot research/rmaf/results/algorithm-x0-core-pilot-replay-new.json.gz --output research/rmaf/results/algorithm-x0-core-extension-replay-new.json.gz
```

The extension wrapper records its measured projection before n5 and refuses
when that projection exceeds two hours. All replay names must be new. Full
data can be large; gzip preserves the per-case partitions, cuts, spans, and
budget results. `results/algorithm-x0-core-packed-v1.json` verifies lossless
packing of the retained original execution records.

Output verdicts are PASS for controls, FIRE for an executed failing instance,
and FINITE-NO-FIRE for complete survival of the declared finite census. The
summary retains every scored denominator. Universal graph/refinement proofs,
Lean proofs and audits, production independence, complexity, and the consuming
rMAF interfaces remain OPEN.
