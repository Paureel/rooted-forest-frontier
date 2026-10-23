# Universal merge checkpoint

The main Lean construction now produces an actual merged family and proves
its exact supports, leaf-label unions, block count and closed cost. This is
author kernel checking; fresh semantic/control/interface review is pending.
Live child restriction and full four-transition correspondence remain open.

`FiniteSelection.lean` constructs a complete duplicate-free enumeration of
the subtype satisfying a predicate. Its nonboundary specialization has length
equal to the previously proved closed cost. `FamilyMerge.lean` uses the index
type `Sum I {j : J // j ≠ p}`: all left indices survive, the distinguished
left index represents the merged block, and all right indices except its
distinguished boundary survive. This is an asymmetric representation of the
symmetric geometric operation. Equal label or color values never identify
other indices.

The output support at the distinguished index is exactly the parent root,
the lifted left open support, and the lifted right open support. Every other
support is its unchanged child support lifted into the parent. The function
proves boundedness, path convexity, liveness, disjointness, coverage and exact
root ownership from the actual child family fields and boundary equations.
It does not assume output-family validity or a block correspondence.

The output index count is `L.blockCount + R.blockCount - 1`; its closed-region
cost is `L.cost + R.cost`. `MergeContract.lean` proves exact support equality
for each surviving index and leaf-label membership union for the merged one.
`merge_universal` exports the actual family witness, exact support equations,
boundary, count and cost without a decidable-equality premise in its statement.
Its proof chooses classical equality for the explicit finite selection.
The concrete `merge` function takes decidable equality on right indices.
No extracted implementation or runtime claim is made.

The separate X0 adversary preceded proof construction. It checked 192 tiny
valid family pairs, all five frozen positive fixtures, four malformed inputs,
four wrong-number/clean-twin pairs and three support-corruption/clean-twin
pairs. A deliberately numeric-blind checker failed the control battery.
These are bounded exact observations, not the universal proof. The two X0
checker methods share their author and specification; fresh-author review is
separate. Its receipt location correction is documented in
`adversary/RECEIPT-LOCATION.md`; receipt bytes did not change.

The main Lean inventories are recorded by module: FiniteSelection has four
queries, FamilyMerge nine, MergeContract seven, and MergeControls fifteen.
The controls construct all five frozen trees through the actual family
operations and check counts, costs, retained vertices, a required stem and
the unused internal vertex. Four separate false claims fail specifically on
their mathematical propositions, with matching correct statements compiled.
The auditor separately rejects an import-error file as a false-goal test.
The source and axiom inventories, compiler commands and timings are in the
new `triple-family-transitions-build-*` receipts. Standard axioms only are
allowed. Failed elaborations and source snapshots remain available; their
placeholder diagnostics are not accepted proof evidence.

The independent geometric route proves rooted path-union, convexity,
boundedness, labels and disjointness statements in its own representation.
The main proof was written without reading that new source and imports none
of it. A distinct finite-index/count route is underway. These supporting
routes do not replace fresh review of the main constructor.

Remaining obligations: fresh acceptance of this merge, actual live child
restriction/reindexing and completeness, normalization-to-restriction support
transport, color/mask legality, executable graph correspondence, automaton
instantiation and Python refinement. No complete G2, unrestricted algorithm,
safe-cover argument, improved exponential bound or novelty result is claimed.
