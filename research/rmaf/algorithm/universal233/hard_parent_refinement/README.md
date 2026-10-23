# Hard-parent refinement

This package proves the actual original hard2 cherry branching cover. It is an author kernel proof awaiting fresh hostile/nonauthor verification. The complete faster rooted-MAF algorithm and all three main algorithm milestones remain OPEN.

Read `RESULT.md` for scope, `INTERFACE.md` for the exact consuming call, and `SOURCE-LEDGER.md` for retained source provenance. The proof accepts `RMAF.agreement` directly and constructs the two actual source cuts and three nonleafless original residual components. No refinement/history/ownership field is supplied by the caller.

Run from the workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/hard_parent_refinement/replay.py
```

`LATEST-RECEIPT.txt` names the read-only final author receipt. The replay rebuilds exact source copies, audits every declaration by original module, checks only standard axioms, and requires deliberate false propositions and audit corruptions to be rejected. The controls are small exact source fixtures, not a finite census.
