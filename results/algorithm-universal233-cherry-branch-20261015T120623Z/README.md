# Ordinary cherry branch proof

The author result proves the actual original t1 no-larger exchange and t>=3
cherry branching cover. Fresh nonauthor verification is pending. The complete
faster algorithm and all three global milestones remain OPEN.

Read RESULT.md and INTERFACE.md. The exact preproof controls and their false
controls are retained with PREPROOF-RECEIPT-v1.json. Rebuild using:

    ./bootloops-python research/rmaf/algorithm/universal233/cherry_branching/replay.py

The replay copies exact pinned sources into a fresh results directory, rebuilds
all modules with an isolated LEAN_PATH, checks actual module origins and
standard axioms, rejects false claims, and catches audit/pin/path corruptions.
The final manifest identifies immutable source/evidence files and the explicit
no-write boundary. Development caches are excluded. The script creates only
new results evidence after the manifest is frozen.
