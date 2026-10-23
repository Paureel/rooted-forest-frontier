# Pair-case geometry

Read REPORT.md and CONSUMER-TRACE.md. `lean/Selector.lean` proves and implements the actual original-address G selector; `lean/Controls.lean` contains literal clean controls. `replay.py` copies accepted sources, recompiles them and performs the complete module-origin axiom audit, five false-proposition checks and the compilable-custom-axiom rejection control. A replay output name is immutable; use a new versioned name in the wrapper before rerunning.

`geometry_controls.py` is a one-shot development wrapper of the dedicated completed X0 checker. It checks frozen dependency/code hashes before import. It is a test instrument, never a production rule or independent verification of its own dependency lineage. Its output is immutable.

Frozen author receipts are `research/rmaf/results/algorithm-pair-case-geometry-formal-v1.json` and `algorithm-pair-case-geometry-controls-v1.json`. All three main algorithm milestones remain OPEN; scoped G needs fresh nonauthor consumer review.
