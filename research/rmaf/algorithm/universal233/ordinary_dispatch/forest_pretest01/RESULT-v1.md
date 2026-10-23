# Full-current-forest exact0/1 author result v1

The full-current-source-forest pretest has a source-bound Lean author proof
of universal cost-zero/one coverage, found global minimality, complete
found behavior, rejection's universal cost-at-least-two bound, and refusal
exactly on malformed input. Fresh independent review remains pending.
All three main algorithm milestones and novelty remain OPEN. The parameter
convention is q=k-1; no rho leaf is implicit.

The program enumerates the unchanged full source-label partition and every
nonroot original edge in exactly one actual current source component. It
checks original `ForestState.agrees` on every entire candidate and selects
minimum actual `ForestState.additionalCost`. It handles target overlap
between different current source components and calls no ordinary solver,
minimum callback, desired-cover record or optimum oracle.

`ForestPretest01.universal_coverage` represents every actual state AF with
additional cost at most one by an enumerated forest of the same cost, up to
inner-label and outer-block permutations. The proof derives each source's
one/two-block representation from its actual source check and frozen
`DepthOne.source_two_split` original-edge geometry. It regroups the full AF
by the unique current source owner and uses the exact source/block cost
balance. `ForestPerm` contains only permutations and their composition;
`agrees_perm` proves invariance of the original full-state Boolean test.
No target-disjointness premise occurs.

The canonical author receipt is
`results/algorithm-universal233-forest-pretest01-replay-20261015T181834296403Z`.
It rebuilt 91 actual pinned source modules, including seven new modules,
and audited all 3,248 stored local declaration-producer occurrences before
coalescence. Of those occurrences, 144 belong to the seven new modules.
The axiom union is `Classical.choice`, `Quot.sound`, and `propext`.
Every Lean process finished within the 30-second cap; the longest measured
process took 6.448 seconds. The 196 processes took 145.873 seconds in total.
The receipt directory contains 35,974,680 bytes at completion; producer
stdout was compressed separately for each audited module.

Executed controls cover internal target overlap, 64 target/source mirror
combinations, empty/singleton/malformed cases, exact cost-two rejection,
and a source-edge omission. The omission still permits another cost-one
answer but loses the specific actual cost-one witness even up to
`ForestPerm`; `Controls.missing_edge_universal_failure` proves that loss.
Four deliberately false mathematical claims were rejected. Fresh producer
controls accepted clean shared-name/type twins in both orders, detected a
same-name/type custom axiom in both orders and private/unused custom axioms,
and caught missing/duplicate rows, wrong module paths and source/adapted
byte changes. Known true/false Std controls passed and failed as pinned.

Five failed development pilots remain retained, including the deliberate
API probe. The failures were fixture/elaboration errors; no scientific
counterexample was removed or overwritten. The prior GenericForest v3
manifest's 540 immutable files were hash-checked before and after replay.

`candidates_count` proves the exact original-edge candidate count and
`candidate_linear_bound` proves at most 1+2n candidates for n current source
leaves. `SOURCE-WORK-v1.md` gives the source primitive, arbitrary-label bit
and output-payload qualifications. A formal instruction-count theorem for
every original agreement primitive, compiled-machine timing theorem,
parent dispatcher integration, independent review, and the full improved
algorithm/exponent remain outside this author result. The toolkit-wide
suite and old AF census were intentionally not run, as pinned.
