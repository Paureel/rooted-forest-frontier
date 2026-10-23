# universal233 geometry proof files

Read `RESULT.md` for exact scope, hypotheses and remaining source-state/core obligations. The full faster algorithm is not proved.

Run from the BootLoops workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/geometry/audit.py
```

The script rebuilds the unchanged original RMAF dependency and four local proof modules with `./bootloops-lean`, checks every source theorem's complete axiom list, rejects two false proposition controls, and records source hashes in `certificate.json`. A successful replay means kernel checking with only standard Lean axioms. It does not constitute independent review, source-core coverage, or full runtime acceptance.

- `Geometry.lean`: actual address graph paths, convex hulls, components, median/Helly, coincidence and abstract final-piece ownership.
- `Bridge.lean`: exact bridge to original RMAF executable minimal spans, original-label colors, realized region counts and a concrete selector.
- `Composition.lean`: actual original agreement ownership covers, refinement facts, conditional source-core selection, and distinct-component cut-list cardinality.
- `Controls.lean`: exact finite vertex-only clique, leafless-middle chain, root and singleton controls.
- `FalseControl.lean`: deliberately false propositions; this file must fail to compile.

The other logs retain failed elaborations and the final author replay. `WORKFILE.md` preserves development history. `referee_sim_RESULT.md` is a pending-review objection table, not a completed fresh-context referee report.
