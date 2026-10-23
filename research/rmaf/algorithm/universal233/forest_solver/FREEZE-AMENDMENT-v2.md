# Freeze amendment

The first manifest included `freeze.log` while the freeze command was still writing its stdout. That entry changed after hashing. Version 1 is preserved, and version 2 excludes mutable freeze stdout logs and pins the freeze script explicitly. The Lean sources, the successful isolated receipt, all theorem statements, all controls, and their source hashes are unchanged.

The current manifest is `FOREST-SOLVER-MANIFEST-v2.json`; its `amends` field pins the original version 1. The version 2 immutable entries are checked again after the freeze command exits. This bookkeeping correction grants no fresh nonauthor acceptance and changes no scientific scope.
