# Mutable receipt pointer

Version 3 excludes `LATEST-REPLAY.txt` from immutable entries because a future replay updates that pointer. The fixed canonical receipt path remains in the manifest. Versions 1 and 2 remain preserved and are linked by the successive `amends` hashes. The Lean sources, successful receipt, controls, theorem statements, and cost qualifications are unchanged.

The current manifest is `FOREST-SOLVER-MANIFEST-v3.json`. Its immutable entries are checked after the freeze command exits; future author or independent rebuilds can create new receipts without altering the canonical one.
