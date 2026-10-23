# Exact leastness adversary

The unchanged RMAF extractor matched an independently constructed graph
oracle in 826 finite Lean equalities. The oracle enumerated every nonempty
ambient subset for each tested case and compared the least connected
terminal-containing subset with an edge-deletion computation. No source/spec
counterexample was found within this stated finite search.

The ten fixed cases include repeated labels, duplicate selections, empty and
absent selections, a selected root leaf, crossing quartet leaves, singleton
and sibling selections, and suppression of an initial root path. Five
deliberate changes were rejected with five unchanged twins passing. In
particular, adding the root above the selected branching point preserves
connectivity and ambient validity while violating leastness.

## Reproduce

From the bootscience root, run:

```sh
./bootloops-python research/rmaf/bridge_review/leastness/adversary/audit.py --name pilot
./bootloops-python research/rmaf/bridge_review/leastness/adversary/audit.py --bound 4 --name bound4
./bootloops-python research/rmaf/bridge_review/leastness/adversary/lean_checks.py
```

The scripts are one-shot problem audits, retained here intentionally. They
use Python's standard library and the project's Lean runtime. The first
script reads controls/frozen.json, constructs graph vertices and edges, then
enumerates connected subsets and deletes edges. The second compiles the
unchanged original RMAF source into this folder, generates exact expected
lists from the frozen fixtures and graph output, and invokes bootloops-lean.

## Evidence

| Check | Exact denominator | Result |
|---|---:|---|
| Fixed graph fixtures | 10 cases, 1,018 ambient subsets | Expected sets reproduced |
| Graph corruptions | 5 corruptions and 5 unchanged twins | Expected distinct failure signatures reproduced |
| Enumerated graph corpus | 816 cases, 85,488 ambient subsets | Edge-deletion and connected-subset sets agree |
| Unchanged Lean extractor | 826 finite equalities | All checked by decide; no axioms reported |
| Semantic false Lean assertions | 2 assertions | Both rejected because the proposition is false |
| Malformed proof of a true equality | 1 assertion | Rejected with a type mismatch |

The corpus includes every ordered full binary tree shape with one through
four leaves, every assignment of labels from {0,1}, and the eight selection
lists [], [0], [1], [0,1], [2], [0,0], [1,1], [0,1,0,1]. The per-leaf case
counts are 16, 32, 128 and 640. Empty-terminal cases check the empty-output
convention; they are excluded from the nonempty-terminal constructor claim.

Pilot timing was 0.00110 seconds for the fixed graph fixtures and corruptions.
The three-leaf graph run took 0.00529 seconds overall; the four-leaf run took
0.0732 seconds. The unchanged RMAF compilation took 5.95 seconds, the ten
Lean fixed checks took 0.376 seconds, and the 816 Lean corpus checks took
3.34 seconds. These measured timings describe this audit on this machine.

## Scope and provenance

controls/frozen.json and receipts/frozen.sha256 predate source inspection.
SOURCE-CONTRACT.md lists source locations, shared implementation layers, and
the limited accidental exposure to three Walk.start proof lines. No new
leastness proof or previous geometry/oracle was read. The source SHA256
receipt and each generated Lean source/log hash are retained.

EDGE-SEPARATION.md gives an ordinary derivation with explicit use conditions.
It remains separate from the executed finite equalities. Universal
constructor certification and the composed region/consumer call require
their own kernel checks and fresh nonauthor review. These adversary fixtures
may guide construction, so they cannot later certify independence from a
construction that used them.

The acceptance gate is exact equality with deliberate semantic failures;
floating-point digit escalation and leave-one-out fitting do not apply to
these finite Boolean/list decisions. The graph oracle's two methods share
its incidence graph and Python runtime; SOURCE-CONTRACT.md states that
common layer explicitly. The project-wide bootloops-check suite was not
run for this isolated proof audit, and no theorem in another arm was checked.
