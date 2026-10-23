# GLOBAL-CB1 fresh adversary instrument

The one-shot scripts test the actual SPEC-CB1 original-edge hitting-set solver,
including initial incidence factorization, dynamic maximal-column quotient,
row minimization and first-success iterative deepening. They do not import or
read the production optimizer. The frozen design and controls preceded all
new construction tests; JOURNAL-CB1-X0.md retains their contact history.

Use `independent_cb1.py` to replay the frozen abstract/ordinary controls. It
independently computes ordinary optima by set partitions and original supports,
then checks every source cutset for the conflict characterization. Use
`pilot_families.py` only for the listed small family pilots. The two
`check_reverse_*.py` files check explicit reverse-caterpillar formulas selected
after those pilots. They are development evidence, not fresh certification.

Outputs distinguish finite executed evidence from the handwritten infinite
family argument. Node counts include failed budgets and every rejected branch;
only one optimum certificate is retained. A script aborts on any mismatch.
The repeated quotient-family proof and source correspondence must receive a
fresh nonauthor review before the result is called VERIFIED-CLOSED. No Lean
closure, runtime improvement, or novelty is claimed.

Replay from workspace root:

    ./bootloops-python research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/independent_cb1.py --controls research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/CONTROLS-frozen-v1.json --output /tmp/cb1-x0-controls-replay.json
    ./bootloops-python research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/pilot_families.py
    ./bootloops-python research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/check_reverse_invariant.py
    ./bootloops-python research/rmaf/algorithm/balanced_safe_cover/continue20261015/adversary/check_reverse_compact.py

Before trusting output, require the six abstract and nine ordinary controls,
all26 deliberate corruption catches, the source-cutset equivalence sweep,
and a fresh source/model/code review. The prototype's partition and conflict
legs share its newly written graph/path representation; that shared layer is
explicitly outside their mutual independence claim. The reverse-caterpillar
proof does not depend on the much larger matched-sector pilot counts.
