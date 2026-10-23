# Conditional coverage of the actual guarded frontier

This is a source-model argument for the implemented proposal. It is pending
independent review and source-bound formalization. The algorithmic alpha bound
remains open. C1/C4 and the normalization lemma have exactly the scope stated
in conflict/PROOF.md; no optimum oracle is assumed by the implementation.

Fix an original optimum cutset K of cardinality q<=b, normalized so that every
original source component has labels. Mathematical existence of K is used in
the proof only. The generator receives S,T,b and explicit graph constraints.

## State invariant

The proof marks at least one path of search states. A state on this path has
actual original prefix C and residual row family R. Only for states known to
extend an original optimum does the proof maintain an original minimum K_C
containing C such that K_C minus C hits R. Conversely every transversal X of R, united with
C, hits the original conflict family. All row universes exclude edges already
in C. The residual minimum is q-|C|: a smaller transversal, united with C, would
contradict original optimality. These properties hold at the root by C1 and
the definition of H. They are
not asserted for every state actually visited. The exact prefixes65 and257
of the quotient-star run have minimum refining cost4 versus original3, as
recorded in SPEC-CB4-ERRATUM-v2.md. The induction only needs one retained
optimum continuation from each marked state.

Row subsumption preserves all transversals. Projecting onto maximal incidence
columns restricts the allowed choices, but maps a minimum remaining witness
to representatives without increasing its size. C stays fixed. The reverse
feasibility direction follows because each projected row is a subset of its
old row. If the mapped union had fewer than q cuts, C1 would contradict the
original minimum. Hence another original optimum containing C survives.

A singleton projected row forces its unique original edge into that surviving
remaining witness. Removing all hit rows and adding the edge to C preserves
the invariant. Every selected edge is absent from subsequent row universes,
so all forced-cut counts are distinct original cuts. The same argument
applies to the structural child closures used by compile_row.

A surviving remaining witness hits the chosen branch row, so it uses some
raw branch edge. That raw branch's prefix P_j and remaining witness X_j give
an original optimum containing C. If the implementation discards it, a
retained child i has |P_i|<=|P_j| and every row of R_i contains a row of R_j.
Thus X_j hits R_i. The union C union P_i union X_j hits the original H and
has at most q cuts. Minimality forces equality, so another ORIGINAL optimum
containing C union P_i survives. Duplicate removal cannot lower the count
below q. Only one minimum must survive; no all-optimum claim is used.

The visited key includes C as well as R and the remaining budget. Identical
row systems with different source forests are not silently merged. Rejecting
an unlabeled source component cannot remove this minimum path: C subset K_C
implies every C-component is a union of the leaf-bearing full original
K_C-components. The path has at most q cuts, so budget pruning also cannot
remove it.

## Guard validity and stopping

The emitted original prefix is checked to induce r+1 nonempty components
for r cuts (the empty input is separate). Original target supports determine
the purity test directly. Rooted restriction comparisons determine the
compatible/triple predicate. Each local witness is either the compatible
whole block or disjoint agreeing pairs and singleton labels. Source and
target supports are checked inside that component. No distinct unused label
leaf can lie internally on another label-pair path.

Connected local supports are assigned distinct regions. Expanding a region
only across an unassigned adjacent original source vertex preserves its
connectivity. Every label is assigned initially. Connectedness guarantees a
frontier until all original component vertices are assigned. Region boundary
edges are original internal source edges; the quotient is a tree on the
nonempty witness blocks, hence exactly pieces-1 such cuts. This is an explicit
local agreement-forest witness. Therefore the ORIGINAL unmarked local
minimum d_D is at most the recorded cost. The emitted upper costs are all at
most floor(b/2). No distance value is recognized by an uncharged optimizer.

If a guard passes on the invariant path, K_C's leaf partition refines the
original forest S-C. This is the actual C subset K_C original-edge reachability
fact proved abstractly in quotient/EdgeLocalization.lean; the graph predicates
are instantiated by the explicit unsuppressed source adjacency and edge masks.
The generated cover therefore preserves at least one original optimum.

If no guard passes earlier, the invariant path reaches a full normalized
original optimum by at most q cuts. Its source components are agreeing and
its target supports are disjoint. The explicit whole-component witnesses
cost zero, so the guard must pass. Thus the finite generator covers every
feasible budget, conditional on the stated actual source-model imports.
Every emitted output is checked even when b is infeasible.

## Missing bound and consumer

Search depth is bounded by the number of counted original cuts; each retained
child adds at least one. All guard construction and failed recognition work
are polynomial in the original input size. The number of states and outputs
is only bounded by the coarse explicit search tree. No alpha5/4 or
prelicensed3/2 bound is proved. Pure-bridge and compatible/triple exact
completion retain their separate source/executable obligations at CONSUMER.
Consequently this is a paid proposal and a coverage argument, not a complete
faster algorithm or an accepted safe-cover theorem.
