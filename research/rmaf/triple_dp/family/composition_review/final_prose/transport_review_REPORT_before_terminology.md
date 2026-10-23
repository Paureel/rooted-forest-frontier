# Fresh transport review

Accepted within the exact forward interface: FamilyTransport constructs actual
CostRoute families from a raw family with no open region, or from a raw family
with a specified live open region. It then constructs such a family from every
normalized raw family, preserving charged cost and labelled-block count. No
circular semantic assumption or proof defect was found. Full G2 remains OPEN.

All author sources and earlier review records were preserved. This review did
not open or modify the revised author report. Its new source snapshots and
hashes are in `source-manifest.json`; the independent replay receipt is
`../../../../results/triple-family-transport-review-replay.json`.

## Exact representation

| Input to the transport constructor | Output index type | Support at each index | Root boundary | Block count / cost |
|---|---|---|---|---|
| RawFamily F with `F.openRegion = none` | `Fin k` | `F.closed i` | none | k / k |
| RawFamily F with `F.openRegion = some R` and `HasLeaf t R` | `Sum (Fin k) Unit` | closed supports at `inl i`; R at `inr ()` | `some (inr ())` | k+1 / k |

The first branch appears at FamilyTransport:36–53. The second appears at
:55–106. These locators refer to the retained source snapshot. The supports
are retained by definition, rather than recovered from a hypothesized block
correspondence. `finIndex` enumerates `List.finRange k` with its nodup and
completeness proofs (:26–29), while `unitIndex` enumerates exactly one element
(:31–34). The open constructor uses the previously reviewed disjoint sum
index enumeration. It never merges indices by label or color.

The two vocabulary conversions are proved by induction on the actual BTree:
`vertex t v ↔ CostRoute.Vertex t v` (:8–15), and
`label t v = some x ↔ CostRoute.LeafAt t v x` (:17–24). The leaf-value equality
has the correct direction in the singleton case. These theorems identify the
vertex and label predicates rather than assuming that the two family models
mean the same thing.

Every output Family field is constructed from an explicit input field and
these conversions. The open constructor's disjointness proof handles the two
cross cases using `F.open_disjoint` and its open/open case using the sole Unit
index (:83–93). Its coverage proof identifies any stored open support Q with
the supplied R by equality of the Option values (:94–100). Its root proof uses
closed-root exclusion and actual open-root membership (:102–106). The closed
constructor rules out the open-coverage alternative using its `none` premise
(:47–53). No output-family validity, cost equality, or support correspondence
is assumed.

The count theorems compute the lengths of the actual enumerations (:108–121).
The cost theorems then use the actual boundary value and those lengths
(:112–128), yielding k rather than relying on natural subtraction to erase
an invalid count. All open indexed regions are live: `HasLeaf t R` is an
explicit constructor premise, used in its labelled field (:80–82). This
constructor therefore does not silently accept a leafless raw open fragment.

`normalized_assembly_exists` (:133–151) chooses the first or second constructor
after inspecting `(normalize F).openRegion`. In the second branch,
`normalize_retained` supplies the required live witness. The earlier
normalization count and cost equalities transfer the two output quantities
back to the original F. The exported existential statement promises exactly
`A.cost = closedCost F ∧ A.blockCount = labelledBlocks F`; it does not contain
an explicit support-map assertion. Exact support preservation is available
from the concrete witness constructors.

In this last theorem the preserved supports are those of `normalize F`.
They need not equal the original raw supports, since normalization may trim
vertices or discard a leafless open fragment. Per-block leaf preservation
continues to come from the previously reviewed normalization interface. This
is the precise sense in which the forward representation debt is now closed.
No inverse, representation bijection, or untrimmed-support bijection follows.

## Executed checks

Before opening transport proof bodies, I froze and independently executed two
explicit graph fixtures: a retained singleton has one block, zero closed cost,
and one closing increment; a cherry with two closed leaf singletons and a raw
root-only open fragment has two blocks and cost two after discarding that
fragment. Both clean fixtures passed and both wrong-cost twins (one and three)
were rejected. `exact_transport_controls.json` retains the exact data. These
are revealed regressions, not new holdouts, and no finite census was run.

The fresh replay compiled all local imports into the new reviewer-owned
`build/` directory through `bootloops-lean`, with workspace `ELAN_HOME` and
Lean 4.35.0. The old-core timing pilot took 0.914 seconds; every subsequent
stage took under one second. All 12 declared stages passed: 11 accepted
compilations and the intended negative compilation. All eleven author-source
hashes matched the v2 author receipt and were unchanged through the replay.

FamilyTransport produced exactly nine axiom queries: seven theorem and two
constructor queries. TransportControls produced two theorem queries. Thus
this continuation contributes eleven queried declarations (nine theorems and
two constructors), supplementing the earlier 39 without altering those old
receipts. The cumulative author-family inventory is 50 declarations: 47
theorems and three constructors. Old dependencies and CostRoute's separate
inventories are not added to that total.

The axiom sets contain only subsets of `propext`, `Quot.sound`, and
`Classical.choice`; the latter enters the normalized existence theorem through
normalization. The source scan found no `sorry`, `admit`, custom `axiom`
declaration, or `native_decide` in the eleven reviewed author/dependency
sources. Exact axiom inventories remain in the replay receipt and logs.

The actual negative diagnostic in `logs/NegativeTransport.log` is:

```
error: Tactic `decide` proved that the proposition
  transportedSingleton.cost = 1
is false
```

The reviewer-owned `CleanTransport.lean` imports exactly `TransportControls`
and proves the matching `transportedSingleton.cost = 0` by decide. It compiled
successfully. The negative check requires the displayed target, one compiler
error, and the explicit false-proposition diagnostic; it does not require
Lean to print the reduced expression `0 = 1`. This review did not rerun or
replace the author's preserved v1 harness failure.

The new source hashes are:

| Source | SHA-256 |
|---|---|
| FamilyTransport.lean | `4cb32e28c7bf4cdcebf186832fe6bdd5f6baf324c7498303278e9509984d86f2` |
| TransportControls.lean | `ba986d23fd8f780c709ba5076638e86a2760d45dd9f7fe42c453a748c62f2315` |
| NegativeTransport.lean | `7a144c4b9a64d4d3bad26756340151b7cd15ab6ab570d753aca2b4e43c6ad15f` |

## Remaining interfaces

The forward normalization-to-assembly representation is established in this
shared finite address-tree model. Universal merge, restriction/completeness,
live-index reindexing, an inverse representation map, good-color/bad-mask
legality, executable graph-hull correspondence, and the Python table and
backpointer connection remain OPEN. Both models still cover every leaf of
the supplied tree. No arbitrary strict relevant-leaf-subset adaptation,
extracted implementation, or general BootLoops-suite result is claimed here.
