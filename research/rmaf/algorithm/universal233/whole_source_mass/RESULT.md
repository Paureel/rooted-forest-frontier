# Whole-source input cardinality and raw mass

Lean accepts the three literal whole-source branch mass bounds below for
every rational base `b >= 2` and every finite generator budget `q`. This is
an author kernel result under explicit source-partition and target-geometry
hypotheses. Independent nonauthor reconstruction and assembly interface
review are pending. All three global algorithm milestones remain OPEN;
no novelty or complete faster algorithm claim is made.

## Exact objects and hypotheses

`WholeColors.lean:8` defines `ParentPartition S A B C`: original source leaf
membership is exactly membership in `A`, `B`, or `C`, and the three parent
label sets are pairwise disjoint. `WholeMass.lean:8` defines `WholeCall` by
that partition, nonempty parents, distinct original target labels, and the
requirement that every source leaf is a target label. Source taxa may be a
subset of target taxa; parent coverage is exact on source leaves.

`WholeMass.lean:16` defines `Occupied D T v` by actual original target span
membership and the requirement that `v` is not a selected leaf of `D`.
No input structure assumes color cardinality, rank or mass. The four-chain
theorem has the explicit geometric gate
`3 <= (VertexGeometry.jointColors B T v w).length`; the diagonal theorem
uses equality to two.

`WholeColors.lean:14` defines the public literal coloring:

    if x ∈ A then 3*ca x else if x ∈ B then 3*cb x+1 else 3*cc x+2

`WholeColors.taggedColor_cardinality` (line 89) proves that the number of
distinct original INPUT colors is exactly the sum of the three actual local
color cardinalities. An empty parent contributes zero. A nonempty untouched
parent with constant-zero local color contributes exactly one.

`OriginalColors.original_colors_cardinality` (line 33) identifies each actual
label-color cardinality with the frozen `regions` list of nonempty original
target leaf regions. `original_colors_at_least_two` consumes occupied
nonlabel span geometry. `original_root_colors_exactly_two` handles the
original target root. `original_joint_cardinality` (line 93) identifies the
literal code `4*colorLabel T v x + colorLabel T w x` with actual `jointColors`.
Its injectivity proof uses the original address-region upper bound of three.

These geometry results are retrieved frozen inputs, not new claims of this
package: `geometry/Bridge.lean:427` gives the two-or-three occupied region
count, line 610 gives the root count, and line 462 defines `jointColors`.
The new bridge transfers them to the literal `dedupNat` input count used by
`source_coverage/RationalMass.lean:186`, `generate_rawQ_mass`.

## Actual generator consumers

`WholeMass.wholeOutputs` (line 66) is the actual output list of
`CoreProgram.generate S (taggedColor ...) q` on the WHOLE source `S`.
The branch lists below are literal list appends. `rawQMass` maps over those
lists and sums every occurrence, including duplicates, using actual
`Output.sourceCuts.length` as the exponent cost.

| Theorem | Whole-source branch colors | Bound |
|---|---|---|
| `clique_raw_mass`, line 85 | two parents cleared at `v`, third untouched; all three choices | `3*b^(-4)` |
| `four_chain_raw_mass`, line 113 | `B(v),C(w)`; joint `B(v,w)`; `A(v),C(w)`; `A(v),B(w)` | `4*b^(-4)` |
| `diagonal_raw_mass`, line 146 | joint `B(v,w)` versus `A(v),C(w)` at actual joint count two | `b^(-3)+b^(-4)` |

For the clique each cleared parent contributes at least two local colors,
so each literal input count is at least five. In the four-chain case the
joint middle input has at least three middle colors plus the two untouched
parent tags, and the other alternatives have two cleared binary parents.
In the diagonal case the literal input counts are at least four and five.
`generate_rawQ_mass` therefore gives exponents `-4`, `-4`, and `(-3,-4)`.
The source parent tags already account for the initial hard2 cuts. These
bounds receive no additional `b^(-2)` factor. The construction uses one
joint middle generator call; it never adds independent same-parent cuts.

## Executed evidence and limits

The receipt
`results/algorithm-universal233-whole-mass-20261015T082345Z/certificate.json`
records a fresh 29-module build in 16.38 seconds and a complete origin
inventory of 1,738 declarations. The observed axiom union is exactly
`propext`, `Quot.sound`, `Classical.choice`. The replay checks the hashes of
all 140 files in the frozen source-coverage manifest before and after use.
No unfinished assembly Lean, core_work, pair_case, or live review source was
read; cut-realization's colliding `Coverage` module was not imported.

Concrete controls recover literal input counts five for a clique, five for
each of the count-three chain alternatives, and four/five for the count-two
diagonal. The root has two occupied colors, an empty parent has zero, and a
singleton label at the root demonstrates why the nonlabel hypothesis is
required. Two equal one-cut output occurrences have raw mass one at base
two. The four corresponding false controls are rejected with explicit false-
proposition diagnostics. The source-pin, omitted-audit-record, and hidden
private-custom-axiom corruptions are rejected alongside clean twins.

The first audit failed because its duplicate-mass false control used an
unreduced rational division. That run is retained under
`results/algorithm-universal233-whole-mass-20261015T082302Z`; the control was
changed to exact `mkRat 1 2`, then the full isolated audit was repeated.
The full toolkit suite and any census were not run: this task uses a focused
Lean proof replay. Fresh adversarial/nonauthor review and a fresh-context
referee simulation have not been performed by this author.

The proved object is conditional mass for actual generator output lists.
The first remaining consumer must compose those calls with original
partition-refinement coverage, target clearing, and realized original cuts.
Deriving the call hypotheses from the actual hard-branch history, proving
the remaining pair case, and proving polynomial implementation work per
prefix remain separate obligations.
