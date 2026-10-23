# Original-edge depth-zero/one pretest

`Pretest.pretest01` refuses repeated or mismatched original labels. On proper
ordinary rooted binary trees, it checks the whole-label forest and the literal
subtree/complement forest of every original nonroot source edge. It returns a
globally minimum original agreement forest of cost zero or one, with the
original cut address. Rejection implies that every original agreement forest
costs at least two. This is an author proof checkpoint; fresh nonauthor
reconstruction and interface review remain pending. All three main milestones
remain OPEN.

Run the source-bound Lean replay from the workspace root:

```
./bootloops-python research/rmaf/algorithm/universal233/depth_one/replay.py
```

Each invocation preserves a fresh replay directory and a new
`results/algorithm-universal233-depth-one-*.json` receipt. The replay uses the
local Lean wrapper, copies and rebuilds all permitted source imports, checks
their frozen pins, inventories all declarations by actual module origin, and
rejects custom axioms. It also runs positive, false, missing-record,
module-origin, foreign-private-axiom, and source-corruption controls.

`Optimality01.lean` contains completeness, global minimum, rejection, and
refusal theorems. `Witness01.lean` supplies full original residual-graph
components, including all suppressed original vertices. `Runtime01.lean`
proves exact candidate counts and structural recursion bounds. `RUNTIME.md`
gives the primitive-operation source audit and its cost-model limits.
`ConsumerControls.lean` applies the theorems directly to the registered
0/1/2-cost and singleton examples. `CONTROL-PIN-v1.json` fixes the controls
used before the universal proof.

`SourceColorControls.lean` directly tests that the crossed two-color quartet
has no budget-one output and has budget-two outputs. Those supplemental
tests were added after the universal author proof; their separate pins record
that timing. The first supplemental false-test draft had an ambiguous name,
and remains as a failed attempt. `FalseSourceColorV3.lean` supplies the
corrected false proposition.

The one-shot development helpers `prepare.py` and `dev.py` are for local
elaboration; use `replay.py` for evidence. `development-history/` preserves
the wrapper records of every early development run, including the failed
elaborations, and later development runs preserve their source snapshots.
