# Forest groups author package

The package proves literal grouped ForestState forward/reverse reconstruction,
exact additional cost, and the retained-A paid-one plus residual-Bforest
specialization. Its status is author proof awaiting independent nonauthor
review; all three main milestones remain OPEN.

Read TARGET-v1.md, RESULT.md, INTERFACE.md, and FIRST-GAP.md. The only geometric
cross-group input compares current source-piece target embeddings; pieces in B
may overlap. Whole-parent target clearance and same-parent source-cut union
are not assumed.

Replay locally from the workspace root:

    ./bootloops-python research/rmaf/algorithm/universal233/forest_groups/replay.py

The replay creates a new results/algorithm-universal233-forest-groups-* receipt,
rebuilds pinned completed original dependencies and this directory's Lean
sources, inventories actual module origins and standard axiom dependencies,
and runs known-true/false and corrupted-copy checks. LATEST-REPLAY.txt identifies
the newest author receipt. FOREST-GROUPS-MANIFEST-v1.json identifies the frozen
canonical receipt and no-write boundary after the author freeze.

prepare.py and precontrols.py were used before proof and are retained for
provenance. They rewrite the development pins and must not be rerun after
freeze. build/ is mutable development output, excluded from the no-write
boundary; frozen sources and receipts must be preserved. The replay is a
one-shot local research driver, intentionally outside the general toolkit.
