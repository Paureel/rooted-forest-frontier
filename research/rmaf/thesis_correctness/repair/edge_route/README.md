# Original-edge normalization adversary

Status: finite NO-FIRE; universal theorem remains OPEN. Proof construction has not begun.

Start with REPORT.md, then results/thesis-correctness-repair-edge-summary.json. The complete reached-root example is first-reached-root-witness.json.

The one-shot checker adversary.py enumerates direct original-edge deletions and checks exact rooted shapes, embedding disjointness, and component containment. run_reached.py records states from the existing algorithm, expands common atoms and restores completed components for source compatibility checks, and restricts E to active original edge IDs. run_structural.py enumerates source-cut-mask states separately. package.py self-replays the saved witness and writes the scoped summary/dashboard checkpoint.

Use the checker for this local repair adversary; it is deliberately independent of previous AF evaluators. Control acceptance requires all four externally frozen fixtures and all four corruption checks to pass exactly. A NO-FIRE receipt means no failure within its explicit finite denominator. It does not prove universal normalization. No sibling component_route work was read.

New tool justification and source/provenance/timing records are in SOURCE-NOTES.md. Source definitions and externally frozen control data are shared dependencies. Independent fresh-author review is still required. This problem-specific instrument is not a new general BootLoops package.

## Construction phase

After the completed adversary phase, the parent authorized the narrowed original-edge proof route. Read CONSTRUCTION.md and PROOF-TARGET.md for that phase; OriginalEdges.lean and RootedPaths.lean provide the scoped formal statements. The formal-audit receipt records an isolated rebuild and positive/negative controls. Universal AF normalization remains open. Earlier adversary records remain the record of their original phase.
