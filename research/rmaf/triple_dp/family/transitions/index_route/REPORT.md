# Independent finite-index route

The finite-index construction and its count equations compile in Lean 4.35.0.
This arm constructs no geometric merge family and makes no claim of full G2
or fresh verification. Its supporting result awaits nonauthor semantic and
interface review.

For arbitrary `I J : Type` with `DecidableEq`, complete duplicate-free
`FiniteIndex I` and `FiniteIndex J`, and designated members `o : I`, `p : J`,
`IndexRoute.lean` constructs `mergedFinite : FiniteIndex (Joined o p)`.
The recursive list `survivors o xs` contains actual values of
`{x : I // x ≠ o}`. The output enumeration consists of one `Joined.boundary`,
then every surviving left index, then every surviving right index.

The namespace is `TripleDP.CostRoute.IndexRoute`. These are the completed
universal statements, with source line locators in `IndexRoute.lean`:

| Statement | Content | Line |
|---|---|---:|
| `mem_survivors`, `survivors_nodup`, `survivors_delete_one` | Exact retained membership, duplicate exclusion, and deletion of exactly one member from a duplicate-free list containing the designated member | 42 |
| `mergedFinite` | Actual complete, duplicate-free merged enumeration | 134 |
| `left_retained_iff`, `right_retained_iff` | A retained child index occurs in the output exactly when its value occurs in its source list | 158 |
| `left_injective`, `right_injective`, `left_right_separate` | Retained child injections and disjoint left/right images | 140 |
| `fromLeft_injective`, `fromRight_injective` | The maps from entire child index types remain injective within each child | 200 |
| `only_boundary_identified` | `fromLeft o p x = fromRight o p y ↔ x = o ∧ y = p` | 218 |
| `all_joined_from_child` | Every merged index comes from a child index | 224 |
| `enumeration_count` | Merged length equals `a.elems.length + b.elems.length - 1` | 176 |
| `closed_complete_iff` | The closed enumeration contains exactly the output indices unequal to the new boundary | 168 |
| `filter_boundary_eq_closed` | Removing the new boundary from the output gives exactly the closed enumeration, including list order | 232 |
| `survivors_are_family_closed` | Forgetting subtype proofs in a child's survivor list gives its actual `Family.closedIndices` when its boundary is designated | 244 |
| `family_closed_count` | For actual children with boundaries `some o`, `some p`, the merged closed enumeration has length `L.cost + R.cost` | 255 |
| `boundary_charge_interpretation` | Subtracting the one new boundary charge from the output length gives exactly its closed-list length | 262 |
| `family_consumer_equations` | Any actual parent family whose finite enumeration is `mergedFinite` and boundary is `some Joined.boundary` has exact block count, exact closed list, and cost sum | 270 |

The last theorem requires a parent family and the two stated equalities of
its fields. It proves its numerical and closed-list conclusions from those
fields; existence of that family and its support, leaf, convexity, coverage,
and disjointness properties remain the geometric constructor's obligations.
No reindexing adapter to another merged-index representation has been proved;
a consumer must use this type and enumeration or establish such an adapter.

The final isolated rebuild is
`research/rmaf/results/triple-family-transitions-index-20261014T142855430197Z`.
It rebuilt `TripleDP`, `ConnectedRegions`, `FamilyAssembly`, and `IndexRoute`
from copied source files. All four modules compiled. The output for all 28
requested declarations names only `propext` and `Quot.sound` (or no axioms).
The source scan found no proof placeholders, custom axiom declarations,
`native_decide`, or unsafe definitions. `summary.json`, `axiom-audit.json`,
`manifest.json`, all source snapshots, commands, and compiler logs are retained.
The nine proof/control invocations took 3.655368333000297 seconds in total.

The controls were written before constructing the enumeration. Their SHA-256 is
`79b3d2d0109044b94547cab61be15b34e954596710a3fb840a519e68cc2bb209`.
All five frozen positive cases compiled as exact Lean list equalities with
exact block/closed counts: `(1,0)`, `(2,1)`, `(3,2)`, `(4,3)`, `(4,3)`.
The final run rejected all three actual false Lean propositions with the
specific `Tactic decide ... is false` diagnostic. The three correct twins
compiled. In particular, the singleton count `2`, singleton charge `1`, and
left/right retained-index collision were each rejected.

The exact Python index checks are retained in
`research/rmaf/results/triple-family-transitions-index-controls-20261014T142441318532Z.json`.
They accepted 5/5 positive cases, rejected 3/3 malformed index inputs and
4/4 wrong outputs, and accepted every corresponding clean twin. An always-true
comparator failed the wrong-output battery. These are author control results
for finite indices; this arm did not rerun the parent geometric support checks.

Failures remain in their original timestamped directories: the first count
proof had two simplification/orientation errors
(`20261014T142234870746Z`); the expanded proof had equality-orientation and
filter simplification errors (`20261014T142441394408Z` and
`20261014T142520560075Z`). Failed elaborations printed `sorryAx` for dependent
unfinished declarations; none appears in the successful final audit.
The first Python control execution failed while writing its receipt because
`Path` lacked the `pathlib` qualifier. That failed attempt counts as no check;
the corrected execution produced the retained receipt above.

The old `FamilyAssembly.lean` was read in full, including its finite-family
semantics and existing filter/count lemmas. This proof uses its definitions
and family fields, and supplies its own subtype enumeration and count proofs;
it does not invoke its cost-count theorem or private deletion lemma. The old
imports and Lean/Std runtime are shared. The parent target and frozen fixture
meanings are also shared. No main `FiniteSelection.lean`, `FamilyMerge.lean`,
`MergeContract.lean`, geometry-route source, or author checker code was read.
Existing proof sources outside this arm's owned paths were unchanged.

Run from the workspace root:

```sh
./bootloops-python research/rmaf/triple_dp/family/transitions/index_route/check_controls.py
./bootloops-python research/rmaf/triple_dp/family/transitions/index_route/run_proof.py
```

The full BootLoops numerical validation suite was not run by this arm. Its
checks concern the supplied toolkit rather than this isolated Lean result.
No external engine or platform-specific check was needed. Two prose review
passes checked the report's scope, counts, terminology, and claim locators;
fresh scientific/referee review is reserved for the parent verification stage.
