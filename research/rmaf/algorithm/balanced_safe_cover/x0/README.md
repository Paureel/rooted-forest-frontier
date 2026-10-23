# Independent X0 finite checker

`exact_x0.py` is a one-shot audit/search instrument written from the model, without reading or importing production/rooted-MAF evaluator code. It enumerates each leaf set partition exactly, compares canonical rooted restrictions, checks unsuppressed vertex supports in both trees, and independently enumerates distinct source-edge cuts by literal connectivity. `cut_graph_replay.py` is a separate no-import replay route: cut both literal graphs, prune label-empty branches, suppress unary vertices, and match labelled component topologies.

Use these scripts for small exact adversarial cases and frozen-control reproduction. They are exponential test instruments, not generators in the proposed algorithm. No optimum oracle may be imported into a safe-cover algorithm from these files.

Outputs are exact integers, partitions, rational values, edge realizations, timings, and explicit verdicts. `REPRODUCES-ALL-FROZEN-CONTROLS` certifies those nine finite fixtures only. `CERTIFIED-CANDIDATE-FAILURE` refutes the stated automatic-preservation rule for its literal witness, never existence of some safe cover. `PIN-MISMATCH` is an audit failure. Finite no-fire is not a proof. The reduction-history eligibility of the witness has not been certified by this arm.

Acceptance is reproduction of every original frozen field, correct rejection of the wrong-topology/coverage/precut/tau/exponent corruptions, acceptance of the clean twin, and full-comparator mutation catches. Final control receipt v3 has 41 exact comparisons, 41 deliberately corrupted comparator calls caught, and six negative detectors. The cut-graph witness route agrees on original optimum, every optimum partition, survivors, total charge, and distinct precut realizations; it was authored by the same X0 agent, so it supplies algorithm diversity but not fresh-nonauthor review.

Replay from workspace root:

```sh
./bootloops-python research/rmaf/algorithm/balanced_safe_cover/x0/exact_x0.py controls --out /tmp/x0-controls.json
./bootloops-python research/rmaf/algorithm/balanced_safe_cover/x0/exact_x0.py search --max-n 4 --pair-limit 25 --equal-halves --require-halfbudget --out /tmp/x0-search.json
./bootloops-python research/rmaf/algorithm/balanced_safe_cover/x0/cut_graph_replay.py --input /tmp/x0-search.json --out /tmp/x0-cut-replay.json
```

Change log, 2026-10-14: initial exact evaluator and controls; bounded n<=3 and n=4 census; full comparator mutations strengthened (failed auxiliary-assertion run preserved in controls-v2); equal-halves/tau follow-up explicitly registered; separate literal-cut witness replay. No toolkit package or upstream verification artifact was changed.
