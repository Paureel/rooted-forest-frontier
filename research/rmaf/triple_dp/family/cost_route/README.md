# Independent indexed-family assembly arm

`FamilyAssembly.lean` constructs families for three transitions: close both
children, extend the left open child, and extend the right open child. Each
family carries an exact finite index enumeration, bounded tree-vertex
supports, path convexity, a labelled leaf in each support, pairwise
disjointness, coverage of every tree leaf, and root membership equivalent to
being the optional open index. The constructor checks these properties.

The child index types form a disjoint sum. Their labels do not identify
indices, so adjacent regions of one color remain distinct unless a separate
merge operation explicitly combines them. Leaf identity is its tree address;
`BTree α` also carries a value at each leaf. No injectivity assumption on those
values is needed for these geometric lemmas. The same-color control uses
distinct `(taxon, color)` leaf values with equal second coordinates.

The count theorem counts the actual enumerated family. `closedIndices` lists
exactly the indices whose supports omit the root, and
`cost_counts_closed_indices` proves that its length equals `Family.cost`.
The three toll theorems therefore count closed supports, including an
explicit charge for each child open support that becomes closed.
`closeBoth_hasLabel_left`, `closeBoth_hasLabel_right`, and
`adjoinRoot_hasLabel` preserve each retained index's leaf-label set.

Run from the workspace root:

```sh
./bootloops-python research/rmaf/triple_dp/family/cost_route/replay.py
```

The replay compiles the two allowed prior modules into this arm's own build
directory, compiles the new assembly and controls, and checks both positive
and negative twins. It retains logs and a source-hashed receipt in
`research/rmaf/results/triple-family-cost-replay*`. Lean must reject the two
count-one mutants specifically with false-proposition diagnostics. Ordinary
compiler or import failures do not pass this negative-control gate.

The producer's grade is **CLOSED-UNVERIFIED for these three assembly
constructors; G2 remains OPEN**. The universal merge transition is not
proved here. The manually constructed merged-cherry fixture only checks its
expected count and charges. The old gapped-region and incursion predicates
are regression controls; the incursion predicate check is not a full-family
trimming check. Fresh nonauthor semantic/axiom/control review is still needed.

The remaining interfaces include restriction/completeness, trimming,
discarding leafless open fragments, color/mask legality, mapping this model
into the consuming DP states/rules, and graph agreement forests. This module
covers every leaf in its supplied `BTree`; adapting a strict relevant-leaf
subset would require an additional model/interface argument. It asserts no
raw-support bijection and no closure of unrestricted rMAF or an exponential
base claim.
