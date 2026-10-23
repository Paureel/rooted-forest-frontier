# First consuming gap: local path extraction

Status: OPEN. This package does not complete Case3.2.2 or the ordinary Rule5
dispatcher. The proved declarations in Case322Cover.lean accept actual original
subtree lookups and label/path incidences. The missing theorem must establish
those inputs for every literal printed local attachment configuration.

The first missing consuming claim is `literal_case322_path_geometry`:

Given proper ordinary original trees T,U, the exact Figure15.2 local attachment
conditions (c and the core C are the two outgoing arcs of the original X hull;
C contains a,b and the remaining S labels), the printed source spine with a
sibling to X, c above that pair and b above c, and the literal selector's path
outputs, derive one of the following, with every original child address kept:

1. Type(i): two distinct selected c-side path-pendant arcs q,r are in
   `cuts T b c`, their original descendant labels lie in X, and an actual
   target descendant subtree W contains c and the deeper arc's labels while
   excluding the shallower arc's labels. These are the arguments `qcut`,
   `rcut`, `lookupU`, `lookupV`, `lower`, `cW`, `uW`, `vW`, `uX`, `vX` of
   `actual_typeI_cover`. The source permits either relative order; an exact
   list-order transport must retain both selected occurrences.
2. Type(ii): each literal outgoing b-path arc, other than the arc to a,
   has an actual ancestor subtree containing b and that arc's labels but
   excluding c; its descendant labels lie in X. This is `bside` in
   `actual_typeII_cover`. The full list, including the six-label example's
   x and y arcs, remains paid. No cost-two theorem is substituted for a+x+y.
3. Type(iii): the actual nonroot LCA subtree contains b,c and its root lies
   on their original path; the actual core subtree contains exactly the
   original labels outside X and c. These are `lookup`, `core`, `coreLabels`,
   `bW`, `cW`, `bC`, `cC`, `onPath` in `actual_typeIII_cover`.

The same extraction must prove `currentGuard` for every materialized branch,
including valid distinct nonroot original arcs, the exact current source
partition and embeddings, and partition.length=cuts.length+1. Current guards
are executed and proved for the three fixed controls, not universally.

A separate missing source-normalization theorem must cover arbitrary sibling
order at each of the three printed source-spine vertices. Current uniform
proofs assume the literal source lookup `(((a,X),c),b)` in that child order;
X and all upward source context are arbitrary. The target cherry includes
both actual sibling orders, target path arcs allow either child direction,
and input-role transport is proved explicitly by `originalCover_roles_swap`.
Finite mirrored controls do not prove the missing source normalization.

This gap is local and does not duplicate the sibling author's global
`admitted -> caterpillar/attachment classification`. Even if that global
classification is supplied, these exact local extraction/orientation and
current-guard consumers still require proof. No rejected hypothesis is
replaced by a saving field or an assumed safe cover.

The source locator is retained split-or-decompose-v2.txt, lines1209–1233,
PDF pp22–23, Figure15 panel2. This is the printed Case3.2.2 path selection
and safety argument. The source's (1,2,2,2) is its worst recurrence from
3(i); the literal controlled costs are (2,1,2,2), (2,1,3), (2,1,2).
