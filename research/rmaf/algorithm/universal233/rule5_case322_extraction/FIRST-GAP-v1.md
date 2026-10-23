# First consuming gap: universal paid branch guard

Status OPEN. The computed original-path plan has a universal original-AF
no-larger cover under actual local source/core geometry. The first unfinished
cost consumer is `literal_rawPlan_currentGuards`, stated in full in
CURRENT-GUARD-TARGET-v1.lean.txt. Its hypotheses include the exact two outgoing
original X-hull boundary arcs, rather than a claimed saving or cover.

`rawPlan_original_cover` permits an empty LCA address because original AF
refinement alone does not certify that an original arc is payable. The
operational caller must prove every `currentGuard` before using the paid
branch budgets. Three facts remain unproved: exact source partition binding
for hard2/singleton branches, paid+1 nonempty current components for every
selected target cut list, and a nonroot fallback LCA from the exact Figure15.2
X-hull boundary. `target_currentGuard_of_nonredundant` proves the other source
partition and embedding checks, but retains the component count explicitly.
That reduction is not a proof of the missing guard.

The post-contact root control has a pendant X subtree, one c-side arc, no
b-side arc other than a, and root LCA. Its current guard is false. It satisfies
the weaker raw-cover hypotheses but violates the exact two-outgoing boundary.
Thus raw-cover correctness cannot be silently promoted to the paid guard.
This control does not refute the printed Case3.2.2 rule.

The preceding release's source sibling and local path-color/order gaps are
resolved here. `bottom_actual_pendants` and `bottom_two_cut_orders` extract
actual source arcs in all eight sibling patterns, with arbitrary X and upward
context. `oriented_split_saving` derives the saving uniformly. Source/core
cluster obstructions handle every selected b-side arc, including S labels.
Actual c-side parent ordering yields the lower original subtree. LCA
lookup/path/label facts are derived from actual original terminal addresses.
`bside_literal_spec`, `cside_literal_spec` and
`bside_without_a_literal_spec` bind the computed predicates to original
path-side arcs and the literal exclusion of the terminal a arc.
`operational_role_binding` transports the entire physical-source state.

The parent retains the global admitted-to-source/core classification and the
marked common-split consumer. Neither was read or duplicated. This local
release does not supply an exact recursive solver. All three main milestones
remain OPEN; zero improved base and no novelty are claimed.
