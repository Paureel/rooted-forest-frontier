# Reproduce the exact embedding checkpoint

The accepted-scope status is in `acceptance.json`. Read `REPORT.md` for the
statement and `USE-SITE-TRACE.md` for every constructor field and original
consumer call. `INDEPENDENCE.json` records shared source and mathematical
lineage. The project aggregate is maintained by the parent research task.

From the repository root, run:

```sh
./bootloops-python research/rmaf/bridge_review/leastness/audit.py
```

This creates a new timestamped audit directory, builds the eight-module Lean
chain with only that directory on `LEAN_PATH`, prints the complete new-declaration
axiom inventory, checks the frozen control hash, runs five deliberate false
propositions and the malformed/clean proof twins, then checks all pinned source
hashes again. A failed build or unexpected diagnostic stops the audit. The
canonical author receipt is `audit/certificate.json`; each run is retained.
The last measured full author run took about 10.5 seconds on this machine.
This is audit execution time, not an MAF algorithm complexity measurement.

The 66 theorem count includes 24 control theorems. The nine additional printed
objects are definitions, not theorems. Independent finite source equalities and
old imported declarations are excluded from this count.

Independent edge-deletion evidence is under `adversary/`. The fresh mathematical
reviewer has its own exact graph-intersection code and clean rebuild under
`fresh_review/`; the independent framing and receipt check is under
`frame_review/`. Each contains its own control and provenance records.

The author driver reuses the preceding executable audit's diagnostic parser.
It is a task-specific instrument, not a new general BootLoops package. Existing
proofs, source definitions, verification scripts and frozen results are
preserved. The project-wide `bootloops-check` suite is not part of this local
Lean-interface audit. All artifacts stay in this workspace.
