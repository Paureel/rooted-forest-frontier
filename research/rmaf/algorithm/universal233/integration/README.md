# Source integration proof files

The full generator and faster algorithm remain OPEN. Read `RESULT.md` for
proved scope and `FIRST-GAP.md` for the remaining original-edge assertion.

Run from the BootLoops workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/integration/replay.py
```

The replay copies all exact Lean dependencies into a new local receipt
directory, rebuilds them with `./bootloops-lean`, audits every explicit
source declaration, rejects three deliberately false propositions, and
retains source hashes and complete logs. A successful run certifies kernel
checking of the listed declarations. Fresh nonauthor review and the remaining
production claims require separate evidence.

| Module | Proved content |
|---|---|
| SourceBridge | Exact Boolean checks to connected actual source partition and original-label owner equivalence |
| Contraction | Actual homogeneous-cherry quotient and exact leaf-owner projection |
| Normalization | Exact executable normalization as a sequence of graph contractions, with full group-payload transport |
| InitialLift | Original source checks and colors composed with the exact normalization call |
| Suppression | Connected supports are convex; suppression embeds actual paths; surviving source partition constructed from terminal hulls |
| EraseLift | Exact executable erase, complete surviving payload lift and singleton owner exclusion |
| Origins | Unique retained original origins and preservation through normalization and erase |
| Branches | Exact chooser occurrences, singleton alternatives and absence of normalized refusal paths |
| CutRecords | Actual attempt guards and local continuation source progress; original cut components remain unproved |
| Controls | Nine positive controls |
| FalseControls | Three false propositions that must fail compilation |

The code is specific to this problem. It extends the frozen modules through
imports without changing their source or replay procedures.
