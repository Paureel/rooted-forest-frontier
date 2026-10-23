# Independent decomposition experiments

These files form a problem-specific experimental instrument. No global improved
running-time bound is claimed.

- **What it does:** `search.py` enumerates rooted binary trees and partitions,
  compares canonical restrictions, and checks vertex-disjoint minimal spans.
  It measures exact minimum forest size on finite instances. `chain_family.py`
  constructs targeted common-chain families. `boundary_search.py` screens
  attachment-state cluster decomposition. `penalty_synthesis.py` mechanically
  screens64 state-penalty tables after two falsified formulations.
- **When to use:** small counterexample searches and regression fixtures for
  new reduction rules. This is exponential in input size and is not the proposed
  FPT algorithm. No code from other route implementations is reused.
- **Meaning:** forests are leaf-set partitions; k counts components. Trees are
  nested binary arrays, no root marker unless an experiment explicitly adds
  one. A `screened-open` result is finite evidence, not a proof. `refuted`
  carries an exact counterexample under these conventions.
- **Acceptance:** frozen `controls.json` must pass first, with positive forests,
  negative forests, and a deliberately false expected optimum caught. Results
  require a fresh implementation to independently verify witnesses and optima;
  they have not yet passed that external gate here.

Replay with the workspace Python wrapper, for example:

```
./bootloops-python research/rmaf/decomposition/search.py
./bootloops-python research/rmaf/decomposition/chain_family.py
./bootloops-python research/rmaf/decomposition/boundary_search.py
./bootloops-python research/rmaf/decomposition/penalty_synthesis.py --family --random-eight 2000
```

`IndependentMinima.lean` contains generic optimization and hypothetical side-count
arithmetic only. Its hypotheses do not discharge the rooted-MAF correspondence
or reduction-safety lemmas. Compilation and axiom audit are recorded separately
in `journal.md` when actually run. See frozen candidate pins, journal receipts,
and `../results/decomposition*.json` for scope and exact execution evidence.

2026-10-14: first instrument version; upstream BootLoops source and pins untouched.
