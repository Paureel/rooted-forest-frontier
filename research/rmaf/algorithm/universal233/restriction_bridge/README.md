# Literal original restriction proofs

Run from the workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/restriction_bridge/replay.py
```

The command snapshots the fixed target, unchanged permitted dependencies, and local proof sources; rebuilds them with an isolated search path; audits every declaration by actual module origin; and runs false/corruption controls. Each run writes a new timestamped replay directory and an `algorithm-universal233-restriction-*` JSON result. It never reads unfinished candidates. A pass is author kernel evidence; fresh nonauthor review is required for a verified closure claim.

See RESULT.md for scope, WORKFILE.md for development evidence, CONTROLS-v1.md for the fixed fixtures, Forward.lean for decomposition, and Reconstruction.lean for reconstruction. Existing logs, source snapshots, and the public target pin must be preserved.
