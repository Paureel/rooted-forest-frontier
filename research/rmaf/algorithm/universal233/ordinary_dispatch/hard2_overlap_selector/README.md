# Actual first-hard2 overlap selector

Author release; independent review pending. The executable selector computes
the three original target hulls and checks their eight possible pair-overlap
patterns. It returns disjoint hulls, a common clique vertex, a two-overlap
chain with actual jointColors count 2 or at least 3, or an isolated overlap
pair with an actual PairGeometry.choose result. Its data constructors contain
only original addresses, a literal parent order and the pair selector data.
No cover, mass, classification proof or optimum oracle is a runtime field.

`select_exhaustive` proves a result and all original geometric guards from
target leaf uniqueness, source-to-target label inclusion and the literal
checked three-parent source partition. Nonempty parents and label disjointness
follow from that checker. Existing actual hull Helly, joint-color dichotomy
and pair-selector completeness proofs are reused. The four literal parent
orders suffice for all eight overlap patterns; parents_perm proves each
reordering is a permutation of the original P.

`actual_hard2_exhaustive` starts with actual CherryBranching.select=hard2 and
DepthOne.proper. It constructs the two original source cuts, actual residual
source geometry, checked source partition and source embeddings before
quantifying over an unknown final forest. `actual_source_inputs` also proves
that this P is the literal pendantPartition. No Rule5 admission is assumed.

The actual clique, four-chain, diagonal and vertex-pair consuming theorems
derive their geometric guards from the selected result and call completed
cover/mass interfaces. Chain and pair reorderings transport refinement back
to the original P. The original unknown forest F, endpoint alternatives,
outputs, paid source cuts and budget q remain literal. Their existing bounds
are respectively 3*c^-4, 4*c^-4, c^-3+c^-4 and c^-3+c^-4, under c>=2.
These local inequalities do not establish the whole algorithm exponent.

`selected_pair_guards` supplies actual PairGeometry.choose, ValidChoice,
properInput, distinct parents, permuted source partition/embeddings and every
other-parent clearance guard for the isolated case. The edge choice retains
its original edge, side-label nonemptiness and actual clearance through the
completed ValidChoice definition. No source-core surgery is repeated here.

`actual_disjoint_admission_iff` uses the frozen priority bridge to reduce
actual Rule5 admission to the literal good-block count=2. Target and source
embeddings are proved. The count is retained; the disjoint control with three
good blocks confirms it cannot simply be replaced by 2.

The original first-hard2 countercase now executes this selector. It returns
Order.acb, meaning original parents (A,C,B), and vertex [false,false,false].
The two overlapping parents are bad. The completed vertex-pair paid cover
and mass apply through actual_vertex_pair_paid. One guessed shorter vertex
address failed; its source/log and the bounded literal probe are retained.

LATEST-REPLAY-v1.json pins the canonical nine-module audit. It retains 193
new stored occurrences, full nonproof bodies, actual theorem proof references
and their AX closure, with the standard three Lean axioms. The 318 frozen
source/olean dependency pairs are readonly hard links checked before and
after; none was compiled or mutated. Four precontrol and seven selector false
claims were rejected. All failed attempts remain. Imported declarations were
not freshly rebuilt or re-audited.

All main algorithm, correctness, base, recurrence, runtime and novelty
milestones remain OPEN. Independent credit is 0. The conditional c=2.33
target and initial q=k_opt-1 convention remain; no implicit rho is introduced.
