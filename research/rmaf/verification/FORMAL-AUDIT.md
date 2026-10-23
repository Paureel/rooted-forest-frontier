# Fresh semantic audit of the formal core

2026-10-14. The edge-cut implementation was frozen and executed before
`lean/RMAF.lean` was read. No discovery Python source or algorithm arguments
were read. This review concerns the formal interface, not proof replacement.

The executable definitions retain two distinct notions correctly:
`restrict` suppresses unary vertices for comparing component topology;
`minimalVertices` retains intervening path vertices between the selected
leaves and their LCA for vertex-disjointness. It omits the path above the LCA.
`sameShape` allows arbitrary child swaps, matching non-plane rooted trees.
`partitionCheck` requires nonempty blocks, coverage of labels, and single
occurrences of each label. Under well-formed distinct-label inputs these
definitions match the stated ordinary, no-rho convention at inspection level.

`assignment_solver_optimal` proves optimality over the supplied executable
assignment model and assumes a winner was returned. It does not by itself
establish existence for every intended input, equivalence to a separately
defined graph-theoretic agreement forest, or a smaller exponential running
time. Its own comment discloses the separate interface obligation.

The following obligations remain before calling this a formalized general
rooted-MAF solver:

1. Define input well-formedness: distinct leaf labels and the same label set.
   `Tree` itself permits repeated labels. `partitionCheck` does not enforce
   input-label uniqueness: a duplicate-label input can pass coverage of a
   single occurrence in its block list. Thus a well-formedness predicate is
   necessary at the theorem interface, even though finite controls use valid
   trees.
2. Either constrain labels to exactly `0,...,n-1` or formalize a bijective
   relabeling. `blocks` contains only those labels. Arbitrary natural-number
   leaf labels are not covered by `solve n` without relabeling.
3. Prove that every well-formed partition has a bounded assignment encoding;
   together with singleton forest validity, this gives solver existence.
4. Prove `restrictionAgrees`/`minimalVertices` equivalence to the independent
   rooted-isomorphism and minimal-embedding definitions from the problem.
5. Any proposed improved algorithm needs its own reduction/branch-completeness,
   termination, and worst-case cost theorems. Exhaustive `n^n` assignments
   provide a finite-search core, not the requested `O*(c^k)` improvement.

The finite formal controls are independently replayed by edge deletion in
`audit_formal_controls.py`: the displayed four-leaf instance has optimum 2,
but isolating endpoint 0 or 1 costs at least 3. The crossed-pair overlap plant
is rejected. This supports a concrete refutation under the shared convention;
it does not close the model-equivalence or universal-complexity obligations.

Kernel compilation and axiom audits are separate evidence owned by the Lean
setup arm. This document records a semantic review only.
