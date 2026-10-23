# Common-cherry author completion

Read TARGET-v1.md, RESULT.md, CONSUMER-TRACE.md, and OPEN-CONSUMER-v1.md.
The theorem statements are in StateExpand.lean; the exact original-address
embedding proof is in Endpoint.lean. The canonical receipt is named in
LATEST-REPLAY.txt. Reproduce the source-bound author checks with:

```sh
./bootloops-python research/rmaf/algorithm/universal233/state_cherry_completion/replay.py
```

Each replay creates a new timestamped result directory, rebuilds all 23 local
modules from pinned sources, inventories all module origins and allowed
axioms, and runs positive, false, hidden-axiom, missing-record, wrong-origin,
wrong-path, and source-corruption controls. A successful author replay does
not replace fresh nonauthor acceptance. All main solver milestones stay OPEN.

The preproof graph controls and their receipt are retained under preproof/.
Those controls ran before the new proof. Files under preproof/ and generated
olean files are development outputs, excluded from the immutable source
manifest. Preserve the completed source freeze and canonical result files.
