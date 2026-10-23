# Independent graph route

This directory contains an adversary-first bounded checker, a graph deletion
argument, and a universal Lean theorem propagating degree two from a component
support to a selected piece. All vertices are unsuppressed Boolean addresses.
The full refinement and `clearRest` instance remain formally incomplete.

Use this record to examine the degree-two increment. The checker is specific to
this audit and is intentionally not registered as a general toolkit package.
For actual extractor leastness, use the completed `bridge_review/leastness/`
record. For the unproved transport statement, read `TRANSPORT-OPEN.md`.

Run from the workspace root:

```
./bootloops-python research/rmaf/bridge_review/degree_two/graph_route/checker.py
./bootloops-python research/rmaf/bridge_review/degree_two/graph_route/replay_final.py
```

The first command reproduces the frozen hand controls, then the small bounded
hunt. It overwrites its output files; copy the directory before replaying if the
original timing/hash receipts must remain unchanged. A positive result means no
counterexample was found in that finite panel. The second command rebuilds the
pinned completed dependencies and final new Lean modules, rejects unexpected
axioms, and requires all six false Lean controls to fail for explicit falsity.
Compilation is evidence only for the declarations that compiled.

The first evidence files are `control-freeze.sha256`, `pilot-freeze.sha256`, and
`route-freeze.sha256`; they establish the control/search/proof order. The final
sources and logs are bound in `formal-receipt.json` and `final-freeze.sha256`.
The original failed elaboration attempts remain under `build/` as diagnostics.
They are excluded from proof evidence. No theorem uses a placeholder or a custom
axiom in the final modules.

Before accepting this arm, a nonauthor must reconstruct its exact fixtures with
fresh code, rebuild the final sources, review the ordinary transport derivation,
and inspect the `clearRest` hypotheses. These independent checks are pending.
