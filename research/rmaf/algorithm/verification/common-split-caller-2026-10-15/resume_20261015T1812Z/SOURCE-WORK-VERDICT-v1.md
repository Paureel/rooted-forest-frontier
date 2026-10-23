# Source work verdict

The exact caller proves callback accounting and candidate cardinality. A complete numerical source-operation bound remains OPEN. I read the actual definitions below and did not infer their work from the callback mass or the number of candidates.

`CallerResources.lean:8` proves two q-1 jobs have mass 2/c for positive q; the empty q0 list has mass 0. `GuardedExact.lean:76` restricts that list by the real ordinary outside test and proves mass≤1 for rational c≥2. The exact unpruned value at233/100 is200/233, as checked in every admitted positive finite readout and in the retained rational theorem. `CallerResources.lean:47` proves the full Cartesian candidate count|FM|*|FN|, including invalid guesses and duplicate values.

The remaining source obligations are concrete:

| Actual source | Operations that a complete bound must charge |
|---|---|
| `Marked.lean:7`, `CallerSetup.lean:8` | The caller receives ten actual trees; the source consumer must pay their restrictions, relabelling, marker choice, original cut lookup and guards. Stored proof fields do not make construction free. |
| `Pretest.lean:8`–`:49` | Both outside tests traverse original vertices/edges, build address lists, look up subtrees, construct complements, check proper labels, check each literal candidate and select a minimum. Recomputations inside complement/forest expressions need explicit treatment. |
| `OutsideDefs.lean:5`–`:18` | Marked rejection prepends the representative singleton and relabels the actual outside forest. q0 still has the real outside computation in the source; zero recursive jobs does not imply zero local work. |
| `PaidDefs.lean:12`–`:23` | Allocate the job list, evaluate actual callbacks, retain their payloads, test actual stability, reconstruct and compare output cut cost with q. Callback work and returned payload bounds need the same accounting convention. |
| `Rename.lean:9`, `CallerDefs.lean:7` | Relabel every returned label; materialize GM/GN, traverse all owner pairs, filter heads by original colors, compare whole blocks while erasing once, copy/append remainders and materialize every resulting forest. Invalid candidates incur this work. |
| `RMAF.lean:149`–`:158` | Recompute original leaves, nonemptiness, flatten/count/membership and partition checks on both original trees. Failed candidates must be counted through the point of rejection. |
| `RMAF.lean:84`, `:116`, `:126`, `:138`, `:144` | Recompute restrictions, rooted topology comparisons, full original path spans/minimal hulls and pairwise embedding disjointness. Hull recomputation occurs for block pairs; no constant-cost checker primitive is justified. |
| `RMAF.lean:36`, `:211` | The shape recursion can inspect Cartesian pairs of tree nodes. The selector examines the full candidate list, retains minimum candidates and evaluates actual length costs. |
| All Nat/list/address operations | Maximum label/budget bit length, address length/copying, list equality and allocation must be accounted for in the chosen source model. |

Successful IH replies have AF partition validity, so their total label payload equals the corresponding ordinary or marked label set. That inference follows from `BoundedExact` and `partitionCheck`; it does not bound arbitrary untrusted callback payloads. The deliberate duplicated-list control receives no AF-payload bound. No numerical polynomial envelope or compiler instruction bound is established here.

The full operation bridge must connect these actual loops to one declared primitive and bit model and combine them with Setup construction, source selection and the mutual recurrence. The final original-cut recovery remains external and must be called once after global forest selection. Its retained exponential envelope cannot be charged as a polynomial toll at every recursive node. Runtime below 2.3391, the global recurrence/base and full algorithm remain OPEN.
