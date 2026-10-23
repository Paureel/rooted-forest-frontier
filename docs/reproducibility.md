# Reproduction

## Default finite checks

Run `make check` with Python 3.12+, Git, make and a POSIX shell. The
standard-library wrapper reuses the original leaf-partition and edge-cut
evaluators without modifying them.
It first runs their existing positive/negative controls and the production
comparator mutation. It then recomputes edge-cut component optima and complete
optimum leaf partitions and compares them with the preserved leaf-partition
results on the 3- and 4-leaf corpus. The exact baseline recurrence script
includes a false upper-base control and its clean twin. These are finite
regression checks, not held-out certification of a
new algorithm or a proof of a smaller base.

The preserved comparator prints a fixed n=3..5 scope label. The new wrapper's
`.verification/<run>/actual-coverage.json` records and checks the actual domain:
9 ordered 3-leaf pairs and 225 ordered 4-leaf pairs. Use that sidecar and the
comparison's batch records for coverage; the imported comparator stays unchanged.

The wrapper copies only the required files into a temporary directory and
retains fresh stdout/receipts under .verification/. It does not overwrite the
imported controls, result corpus, journals or dashboard progress. The included
manifest verifies the initial imported file bytes; newly generated setup docs
and wrappers are tracked by Git rather than that import manifest.

`make verify-manifest` checks all initial imported hashes and the 1 MiB limit.
`make verify-small` runs only the finite checks. The local bootstrap verification
receipt is in docs/import/bootstrap-verification.json once executed.
GitHub Actions runs make check on push/PR and offers a manual scoped Lean job.

## Python and local dashboard

```sh
make setup
./bootloops-python your_script.py
make toolkit
./bootloops-dashboard
```

The setup creates a local .venv and installs the small dashboard dependency.
The dashboard also requires `make toolkit` because it reads the pinned
toolkit's source index at startup.
The portable launchers execute commands directly. Automatic launcher recording
described in the imported dashboard README belongs to the original workspace.
The dashboard can discover eligible live processes, but these launchers do not
automatically capture their stdout, exit status or internal stages.
The Python launcher also works with `BOOTLOOPS_PYTHON=/absolute/path/to/python`
and otherwise uses a local virtual environment or python3 on PATH. Root paths
are derived from the checkout. Historical research scripts may still contain
original absolute paths; keep their frozen bytes and add an explicit adapter
or new version rather than editing old receipts.

requirements.lock.txt preserves the original scientific environment. Some
packages there need native dependencies; it is not installed by the default
check. Add the dependencies required by a scoped replay to your local
environment and record the versions and missing engines.

## BootLoops toolkit

The external toolkit is pinned in installation.json and is not vendored.
`make toolkit` clones the original official sources at those exact commits
into ignored bootloops/ and bootloops-skills/ directories. Existing checkouts
are not reset. Consult bootloops/tools/README.md, the relevant GUIDE.md and
the installed protocols before scientific work. ./bootloops-check runs the
supplied upstream suite and retains its original failures/refusals; external
engine legs can need extra setup. The imported installation records describe
the original machine and are not a fresh validation of your clone.

## Scoped Lean check

The archived root model pins leanprover/lean4:v4.35.0. Install that toolchain
with the official elan installer, then run `make verify-formal`. The launcher
uses a local .runtime/elan install when available, otherwise elan on PATH.
This target runs the existing research/rmaf/lean/audit.py in a temporary
copy. It checks only that model's declarations, axiom inventory and expected
negative control; its remaining graph-semantic and algorithmic obligations
remain open. It does not compile every archived candidate or establish the
complete target bound. Heavier replays need their own exact sources and may
need omitted inputs listed in docs/large-files.md.
