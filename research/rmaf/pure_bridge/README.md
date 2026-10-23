# Pure-bridge research instruments

`check_geometry.py` enumerates removed edges of each source tree, extracts nonempty leaf components, and tests rooted restriction equality and vertex-disjoint graph spans. It then compares the proposed marked elimination against exhaustive combinations of local choices. Use it to search for small counterexamples to pure-bridge completion and role swapping. It is intended for finite research checks, and its exponential enumeration is unsuitable as an FPT implementation.

All costs count additional cuts: the number of final pieces minus the number of initial source components. `opt` raises an error for infeasible marks. In particular, marking a labelled leaf cannot produce a finite optimum. The full run starts with `controls.json`, whose hand-derived exact values were recorded before implementation, and must reject three deliberately invalid controls. A comparison failure raises an exception and prevents writing a success report.

`attack_boundaries.py` tests degree-three marking, a nonpure elimination failure, and pure clique examples through ten source components. It imports the discovery checker, so it is not independent confirmation. The finite expected costs were written in `JOURNAL.md` before execution. The formal two-state repair counterexample uses a separate Lean definition.

`attack_mark_interaction.py` checks two genuine degree-two vertex marks whose individual penalties vanish and whose joint penalty is one. `lean/MarkInteraction.lean` formalizes this finite example using the earlier executable RMAF definitions. It shares their semantic lineage and unresolved graph correspondence.

`lean/PureBridge.lean` contains the formal exchange interface and its proofs. Read `FORMAL.md` before using the statements: graph correspondence, splitting, and role-swap partition equivalence remain obligations. `lean/audit.py` rebuilds with Lean 4.35.0, checks all 24 expected theorem reports, records each theorem's axioms, and requires three false propositions to fail for the expected reason.

Run these commands from the workspace root:

```sh
./bootloops-python research/rmaf/pure_bridge/check_geometry.py --count 20 --output pure-bridge-pilot-replay.json
./bootloops-python research/rmaf/pure_bridge/check_geometry.py --count 5000 --output pure-bridge-adversary-replay.json
./bootloops-python research/rmaf/pure_bridge/attack_boundaries.py
./bootloops-python research/rmaf/pure_bridge/attack_mark_interaction.py
./bootloops-python research/rmaf/pure_bridge/lean/audit.py
```

The original adversary receipt records the hash of `archive/check_geometry-v1.py`; the current checker adds an explicit `require_pure=False` option used only for the excluded-hypothesis attack. The default algorithm is unchanged. Reconstructing the archived version by reversing those two edits reproduced the recorded SHA256 exactly. Existing receipts and the original seven-case control list remain available.

2026-10-14 monitor repair: all three Python instruments now write beneath
`research/rmaf/results/`, where dashboard evidence previews can read them.
Earlier workspace-root receipts are retained and copied byte-for-byte into
that directory. Pre-repair scripts and copy hashes are retained under
`research/rmaf/monitoring/20261014T124259Z/`. A controls-only run wrote
`pure-bridge-path-repair-controls.json` successfully; no new generated cases
were counted. Use a new output name when replaying a frozen census.

The measured 20-instance evaluator pilot took about 0.012 seconds; the 5,000-instance evaluator run took about 3.35 seconds on this host. These times exclude launcher overhead and are recorded in the JSON receipts. The latest complete Lean audit records its own build and replay durations. Any larger or differently distributed computation requires a new timing pilot.

No general BootLoops package provides this problem-specific rooted-MAF functionality. The index and guides were checked before writing it, and the instruments remain in the RMAF research directory. The broader BootLoops validation suite was not run because no toolkit package or upstream verification file was changed. External phylogenetic solvers were not used, and the graph-definition correspondence has not been certified by an independent implementation.
