# Original-cut source-core proof

This local package extends the frozen core, geometry and integration modules. It proves actual original residual components for production outputs and finite-budget monochromatic source refinement coverage. The author replay passes; independent review, raw mass, polynomial implementation work and the complete faster algorithm remain open. See `RESULT.md` and `FIRST-GAP.md`.

Run from the BootLoops workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/cut_realization/replay.py
```

The one-shot replay copies the exact Lean source dependencies into a new local receipt directory, rebuilds each module with `./bootloops-lean`, audits every declaration by module origin, runs positive fixtures, and requires false propositions and deliberate audit corruptions to fail. The result JSON and logs state exactly which checks executed. A passing author replay establishes kernel checking of the retained statements; it does not replace a fresh nonauthor reconstruction or prove the open mass/work bounds.

`ValidPartition.checked_source_core` is the external consumer. It accepts the ordinary distinct-label source and exact partition/embedding/color checks and returns an actual output within `blocks - 1` cuts, together with refinement, original realization, output validity and realized cut bounds. `Interfaces.log` in the frozen receipt prints its full type.

The proof files are problem-specific, and the replay is intentionally a one-shot extension of the existing proof replay procedures. It is not a new toolkit engine. The controls test original-root suppression, a previously detached descendant below a later coarsened group, a wrong-side label assertion, a leafless component and an incorrect literal parent after suppression. The replay also catches missing inventory records, changed source pins and foreign-namespace custom axioms.
