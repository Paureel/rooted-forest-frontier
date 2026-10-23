# Executable interface replay

Run from the workspace root:

```sh
./bootloops-python research/rmaf/bridge_review/executable/audit.py
```

The driver uses `./bootloops-lean`, requires no network, and creates a new
timestamped directory under `audit/`. Only this directory supplies campaign
imports for that run. It builds the unchanged `RMAF`, `PureBridge`, and
`GraphRegion` sources before the two new production files.

The output includes build logs, source hashes, axiom inventories, both
deliberately false proofs, the malformed-proof control, and the diagnostic
parser's planted cases. The driver writes `audit/certificate.json` and
`research/rmaf/results/bridge-executable-lean.json`. A zero exit means these
typed statements and audit controls passed; semantic review and open
mathematical obligations have separate records.

`lean/negative/` and `lean/malformed/` contain intentional failures and must
not be included in a production build. `development/Probe.lean` contains
exploratory API checks, including an unavailable name; it is retained for
provenance and is not a proof artifact.

The initial dependency/hand-control runs and both proof-construction attempts
are retained under `audit/`. The general theorem source uses structural
induction and does not depend on any finite Python search. The audit is
specific to this target and is not promoted as a general BootLoops tool.
