# Actual forest-state reductions

The singleton-source cleanup transition is proved against original RMAF checks. The common-cherry transition remains open. See RESULT.md for exact scope and OPEN-CONSUMER-v1.md for its first missing graph assertion.

Run from the workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/state_reductions/replay.py
```

The one-shot replay copies original RMAF and three completed restriction-bridge modules, adapts only their import names, and rebuilds the local proof modules with an isolated search path. Each run keeps the copied sources, full module-origin and standard-axiom inventory, true/false controls, deliberate corruption controls, compiler logs, and certificate in a new results/algorithm-universal233-state-* directory. LATEST-REPLAY.txt names the current replay. A failed run keeps its directory and failure record.

Use these proofs when a finite forest state contains an actual singleton source component, or when proving common-cherry separation and restriction topology. State.lean checks a proper source-label partition, original target-label partition, actual source containment, original target minimal-embedding disjointness, and each source component's original partition/restriction/minimal-embedding checks. Labels are arbitrary natural numbers. The none target represents the exact empty boundary.

A successful replay confirms kernel checking of the scoped theorems and source-integrity checks. It does not complete the common-cherry transition or supply fresh nonauthor acceptance. The false assertions must fail, the hidden custom axiom must be rejected, and the source/module corruption checks must fire. Fresh nonauthor reconstruction and interface review remain required before verified acceptance. All three main solver milestones remain open.
