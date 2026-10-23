# Paid-cover design and finite rejection instruments

This route supplies executable total finite search, versioned safe-cover
candidates, all paid generation/query budgets, original-source witness
reconstruction, and a retained five-leaf failure of cheapest terminal
precuts. It does not supply an improved rooted-MAF algorithm theorem.

Use it when testing whether a proposed terminal-class precut family preserves
an optimum. The neighboring `algorithm/x0/` is the independent adversary
instrument; `pure_bridge/` and `triple_dp/` are conditional terminal libraries.
Those libraries are disabled in the actual executor pending their documented
interfaces. `REPORT.md` and `CONSUMER-TRACE.md` give the exact admission boundary.

`PIN-v1.md` freezes overlap clearing and its same-budget entry failure.
`PIN-v2.md` freezes cheapest terminal precuts and its five-leaf counterexample.
`PIN-v3.md` freezes all minimal terminal precuts and their full paid cost.
Original pins/results are preserved. The later full cover recovers the
lost witness, but its enumeration cost and printed paid mass do not yield
the requested exponent.

These are one-shot project instruments. The BootLoops toolkit index was read;
it contains no rooted-MAF package. Existing pure-bridge graph primitives and
branching tree enumeration are wrapped unchanged. No existing instrument
generated or charged complete terminal precut frontiers. The new code
implements that function and calls the existing graph engine unchanged.
The wrappers share those graph primitives and are development checks.

Inputs are nested binary pairs of distinct integer labels. A current source
forest is a list of nonempty component trees covering every target label.
No rho leaf or completed-component deletion is implicit. `additional_cuts`
is final blocks minus current source components; initial tree-tree `k` is
the number of final blocks and `q=k-1`. Malformed data raises a parsing exception.
Infeasible budget returns `feasible:false`; it is distinct from a valid
empty forest. Every accepted result contains actual original-source cut
edges and the label partition, checked against both original graphs.

Run with the project runtime from the workspace root:

```sh
./bootloops-python research/rmaf/algorithm/paid_cover/state_cli.py input.json
```

For a fixed budget, `input.json` has `target`, `source` (a forest list), and
`budget`. For an ordinary initial optimization request, use `target` and
`source_tree`, omitting `budget`; every budget from zero through the singleton
upper bound is tested. The algorithm is finite and potentially exponential
in n; do not infer an FPT runtime from this executable.

The controls/pilot scripts and `audit.py` write only new named receipts and
refuse to overwrite existing ones. To replay a frozen receipt, choose a new
destination in a copy of the one-shot driver; do not replace evidence of record.
The recorded executions are:

- `run_cover.py --stage controls`: 27 plants/corruption catches.
- `run_cover.py --stage pilot`: quartet full-budget local-query failure.
- `frontier_cover.py --stage controls`: seven grouped controls including
  the 27-control replay.
- `frontier_cover.py --stage pilot`: 20 mixed-size cases before expansion.
- `frontier_cover.py --stage bounded`: first fire after 54 compared pairs.
- `full_cover.py`: all-frontier recovery and deletion corruption.
- `core_controls.py`: supplementary two- and three-color core controls.
- `audit.py`: ten finite-model theorem axiom prints and a rejected false twin.
- `MassChecks.lean`: four exact integer mass checks with empty axiom lists.

Before acceptance, a nonauthor must reconstruct the graph semantics and
cover code, execute fresh controls, replay Lean, and discharge every universal
obligation in `CONSUMER-TRACE.md`. Current output means finite development
evidence or a kernel theorem in the explicit RMAF model. It never means
unrestricted coverage or an improved bound merely because a process exited.

2026-10-14: created this route, retained the first stopped suppression-control
run and its child-order repair, then froze each organizing change before its
next execution. No upstream toolkit source, verification script, integrity
pin, prior scientific receipt, or other design route was changed.
