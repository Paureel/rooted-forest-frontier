# Full-current-forest depth zero/one pretest

`ForestPretest01.pretest01 T ss` tests an actual current source forest,
including states whose current source hulls overlap in the target. It checks
the unchanged source-label partition and every single original nonroot edge
of one current source tree. Every candidate goes through the original
`ForestState.agrees` test as a complete forest.

Use this subroutine when a caller needs to resolve actual additional cost
zero or one, or establish that every actual agreement forest needs at least
two further cuts. The frozen ordinary DepthOne pretest handles a single
ordinary tree pair; it does not provide the full-state target-clearance
check supplied here.

A `.found F` result carries an actual globally minimum forest with
additional cost at most one. A `.rejected` result means the state is proper
and every actual agreement forest has additional cost at least two.
A `.refused` result is equivalent to `ForestState.proper T ss = false`.
The executable output never calls a minimum callback or a coverage oracle.

`ForestPretestSemantics.lean` exports the result theorems;
`ForestPretest01.universal_coverage` derives complete source-edge coverage for
every actual cost≤1 forest, up to inner-label and outer-block permutations.
`ForestPretestWork.lean` proves the exact candidate count and its linear
bound. `SOURCE-WORK-v1.md` states the source primitive, label-bit and output
payload qualifications.

The pinned controls include target overlap, mirrors of source and target
orientations, empty/singleton/malformed cases, a cost-two rejection witness,
and omission of all first-source edges. The omission still permits another
cheap answer but fails universal coverage of a specific actual cost-one
forest. `ForestPretest01.Controls.missing_edge_universal_failure` proves this
failure for the explicit inner/outer permutation relation. Four deliberately
false executable claims must fail kernel reduction.

Run `./bootloops-python research/rmaf/algorithm/universal233/ordinary_dispatch/forest_pretest01/replay.py`
from the project root for an isolated source rebuild and stored-producer
replay. Every Lean module has a 30-second cap. The replay verifies source
pins, executes fresh detector controls, rejects false mathematical controls,
and streams every imported local module's stored declaration producer to a
bounded gzip receipt. It retains failures. Resource limits are pinned in
`AUDIT-RESOURCE-PIN-v1.md`.

This package is problem-specific author work. It adds no reusable general
BootLoops tool. Fresh independent review and the parent algorithm's
integration remain separate requirements. All three main algorithm
milestones and novelty remain OPEN; q=k-1 and no implicit rho is used.
