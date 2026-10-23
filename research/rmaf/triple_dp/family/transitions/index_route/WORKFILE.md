# Independent finite-index route workfile

Opened 2026-10-14. Target read before construction. Owner: merge_index_route.

Route lock: construct a fresh disjoint enumeration from retained left indices,
retained right indices, and a new boundary representative. Prove no duplicates,
completeness, exact surviving-index inclusions/injections, and finite-count and
boundary-charge equations. Shared finite-family semantics may be read, but no
main FiniteSelection.lean, FamilyMerge.lean, MergeContract.lean, geometry_route,
or author checker code will be read. This is a supporting universal indexing
proof; it does not claim a geometric merge family or full G2.

Controls will be frozen before construction, including singleton, extras,
same-spelling source index collision, malformed data, wrong result, actual false
Lean proposition, and correct twins. No custom axioms, sorry, or native_decide.

## Frozen controls and shared semantics

Controls frozen before implementation: controls.json SHA-256
79b3d2d0109044b94547cab61be15b34e954596710a3fb840a519e68cc2bb209.
Five exact positive enumerations; three malformed inputs with clean twins;
four wrong results with clean twins; three actual false Lean propositions
with positive twins. Parent geometry controls are shared specification data,
not an independent oracle. X0 completion is received from parent, not rerun
or freshly verified by this arm.

Read FamilyAssembly.lean (shared semantics): FiniteIndex has elems, nodup,
and complete; Family.blockCount is elems.length; Family.cost subtracts
boundaryCharge; Family.closedIndices filters the designated boundary and
cost_counts_closed_indices gives its exact length. This route will supply
its own recursion omitting the designated member, plus a three-constructor
merged index type; it will not reuse private filtering/count proofs.

Toolkit consultation: bootloops/tools/README.md and capability searches in
external/TOOLS.md and ours/README.md identify no finite-family Lean merger.
Use the existing ./bootloops-lean runtime and shared FamilyAssembly types,
with problem-specific new proof/control files; no toolkit changes needed.
Timing: first isolated import rebuild is the pilot. Runtime unknown until
measured; no long-run projection or larger search is proposed. Progress unit
is kernel-accepted named statements and executed registered controls.

## Executed development receipts

Initial isolated rebuild and three false propositions/clean twins all behaved as
registered: research/rmaf/results/triple-family-transitions-index-20261014T142018923791Z.
First universal proof compile retained a failure at the deletion-length lemma:
research/rmaf/results/triple-family-transitions-index-20261014T142234870746Z.
Two simplification/orientation errors were repaired; no theorem weakened.
The repaired proof and controls compiled in
research/rmaf/results/triple-family-transitions-index-20261014T142329145295Z.
Pilot complete rebuild plus four control subprocesses took about 3.5 seconds;
local theorem compile took 0.48 seconds. These are observed timings, not forecasts.

The first Python fixture harness finished its comparisons but failed while
serializing its receipt: NameError at line 56 (Path was not qualified as
pathlib.Path). This was infrastructure failure, not a passed control run.
It is corrected and will be rerun before any count is reported.

## Completed supporting proof

Final proof source SHA-256:
f4a0a1b987f4e8084c81e9c352c9a1998eefba15d1f94d01a2b74919e87e3a4a.
Final isolated rebuild and complete Lean controls:
research/rmaf/results/triple-family-transitions-index-20261014T142855430197Z.
Its summary reports 4 compiled modules, 3 false Lean controls rejected,
3 clean-twin propositions accepted, 5 positive exact-enumeration cases,
and 28/28 axiom reports containing only Quot.sound/propext.

Additional retained failed proof attempts:
20261014T142441394408Z (two disequality orientation errors, list-filter goal),
20261014T142520560075Z (remaining filter-all goal). Each was repaired without
changing the claim. Successful intermediate final-form attempts:
20261014T142629537667Z and 20261014T142811066889Z. The final revision removes
the consumer theorem's use of shared cost_counts_closed_indices, using our
own boundary_charge_interpretation instead; no old count lemma is invoked.

Exact fixture receipt:
research/rmaf/results/triple-family-transitions-index-controls-20261014T142441318532Z.json.
Verbatim summary quantities: positive 5, malformed 3, wrong_result 4,
planted_broken_comparator_caught true, passed true.

REPORT.md gives the precise conditional family interface, proof locators,
shared-source lineage, all checks and missing geometric/fresh-review work.
This arm is a completed supporting proof, pending nonauthor review; it does
not claim universal geometric merge or full G2. No child agent was spawned.
