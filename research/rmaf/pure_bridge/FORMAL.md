# Pure-bridge formal scope

Lean 4.35.0 checks 24 theorems across two files. The 16 theorems in `lean/PureBridge.lean` import only `Std`. The eight theorems in `lean/MarkInteraction.lean` use the existing `research/rmaf/lean/RMAF.lean` executable definitions to check a concrete marked counterexample. The build, axiom inventory, source hashes, and three rejected false proofs are retained in `lean/audit/`. Theorems may depend on Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms or unfinished proofs occur.

The formal results establish a deepest-root property for path-convex regions, exact conditional exchange identities, and component-count arithmetic. The correspondence between these objects and graph-theoretic agreement forests remains open. A compiled conditional identity does not establish its graph hypotheses.

## Proven statements

A `RootedRegion` has a binary address as root and a predicate describing its vertices. Every member descends from the root, and every vertex between the root and a member also belongs to the region. If two such regions intersect and the first root is at least as deep as the second, `deepest_root_in_neighbor` proves that the second contains the first root. Consequently all neighbors of a deepest region intersect at that root. This theorem places no bound on the number of neighbors.

An `ExchangeSystem A R` describes a local choice `a : A` and an entire remaining state `r : R`. Both choices have validity predicates and natural-number cut costs. Avoiding the common vertex on either side suffices for compatibility. Compatible choices cannot both occupy the vertex. The final field, `clearRest`, requires every valid remaining state to admit an avoiding replacement whose total cost increases by at most one. All existing marks and all remaining interactions are included in `restValid`.

Let `mu` be the attained local minimum. If an avoiding local witness attains `mu`, `free_minimum` proves that the global minimum equals `mu + nu`, where `nu` is the unrestricted remaining minimum. Otherwise suppose every avoiding local witness has cost strictly greater than `mu`. Then `paid_minimum` proves that the global minimum equals `mu + nu`, where `nu` is the remaining minimum with avoidance imposed. Neither theorem assumes additive mark penalties.

The exchange proof makes one case distinction. If the original remaining state avoids the vertex, retain it and replace the local choice by a minimum witness. Otherwise compatibility forces the original local choice to avoid the vertex, so it costs at least `mu+1`. Use `clearRest` once, then replace the local choice by the minimum witness. The saved local cut covers the possible extra remaining cut. This reasoning applies to the whole remaining state even when the neighborhood is a large clique.

For any common feasible partition family with at least `r≥1` pieces per partition, `role_swap_minimum` proves that a minimum of `pieces−1` equal to `h` induces a minimum of `pieces−r` equal to `h+1−r`. `role_swap_parameter` proves that this residual is at most `d` if `h≤d+r−1`. `bounded_second_query` proves the corresponding budget bound when extra marks increase the number of nonempty regions. `negative_budget_impossible` rejects a query whose piece budget is smaller than its region count.

## Remaining graph proofs

The following obligations are required to use the exchange theorem for the intended completion problem. Each statement refers to ordinary rooted MAF with no added root leaf.

| ID | Required statement | Formal consumer |
|---|---|---|
| G1 | The unsuppressed minimal embedding of a nonempty label subset is a `RootedRegion` under a label-preserving binary-address representation. | `deepest_root_in_neighbor` |
| G2 | If two disjoint-label embeddings overlap only at vertices of degree two in each, every block meeting their overlap uses its whole path. Avoiding one overlap vertex therefore avoids the other complete embedding. | `freeLeft`, `freeRight` |
| G3 | If a valid agreement piece uses a degree-two vertex of its component embedding, the labels on the two sides form a nonempty two-piece agreement refinement. The refinement avoids that vertex and preserves every prior mark and every other disjoint piece. | Local one-cut bound and `clearRest` |
| G4 | In a global forest, at most one piece uses a fixed vertex; applying G3 to that piece preserves global feasibility. | `clearRest` for the entire remainder |
| G5 | Deleting marked vertices and discarding leafless regions gives precisely the common refinements of the source tree and the forest of target restrictions to the nonempty regions, including embedding-disjointness under suppression. | Common partition family in `role_swap_minimum` |
| G6 | The region leaf partition can be represented by `r−1` target-edge cuts even when deleted vertices leave leafless intermediate regions. Refining an ordinary `d`-cut forest by those cuts adds at most `r−1` pieces. | Hypothesis `h≤d+r−1` |
| G7 | The implementation supplies attained exact marked minima and implements each elimination invariant, including compatibility with previously fixed witnesses. | Recursive algorithm correctness |

The existing research note proposes arguments for G2–G6 in Sections 2–4. Those arguments were read as candidate mathematics. G1–G7 have not been connected to the Lean exchange structures. In particular, replacing `clearRest` by separate per-component penalties would change the theorem and would not follow from the finite checks.

## Necessary hypotheses

The exact finite checks expose two failures outside the proposed regime. For target and source `((0,1),2)`, marking the internal `(0,1)` vertex raises the local cut optimum from zero to two. That vertex has degree three in the component embedding. The one-cut statement therefore cannot be extended to every unlabeled vertex.

For target `((0,1),((2,3),(4,5)))`, use source components `(2,4)` and `((0,1),(3,5))`. Keeping `(2,4)` intact forces the second component into `{0,1}`, `{3}`, and `{5}`, costing two cuts. Splitting `(2,4)` into two singletons and leaving the second component intact costs one cut and is optimal. The overlap contains a vertex of degree three in the second embedding, so the proposed pure-bridge theorem does not apply. The numerical values and witnesses are in `results/pure-bridge-boundaries.json`.

Lean also checks a two-state countermodel to omitting `clearRest`'s one-cut bound. Occupying the common vertex costs zero on either side; clearing the local side costs one and clearing the remaining side costs two. Its global optimum is one, whereas fixing the minimum local occupant gives optimum two. The false-control file attempts to prove a one-cut repair exists and is rejected with the message that the proposition is false.

Separate zero-penalty vertex queries do not determine their joint penalty. Set target `((0,3),(1,(2,4)))` and source `((0,2),1)`. Mark the parent of leaf 0 and the parent of leaf 2. Both vertices have degree two in the target embedding of source labels `{0,1,2}`. The ordinary, first-mark, second-mark, and joint-mark cut optima are respectively `1,1,1,2`. For the first mark, `{0}|{1,2}` is optimal; for the second, `{0,1}|{2}` is optimal. Both marks together force three singletons. `MarkInteraction.lean` checks these exact values and proves that every feasible bounded assignment for the joint marks has cost at least two. The corresponding false statement that the joint optimum equals one is rejected by Lean.

## Independent review

The Python checks use a new explicit graph implementation and enumerate removed source edges. They share no implementation with the earlier RMAF oracles. Within this implementation, local optimization, role swapping, and global comparison share graph paths and restriction shapes. These are discovery comparisons; a second author must reconstruct the semantics and the exact examples before scientific acceptance.

The marked Lean example imports the earlier executable model after the Python example was found. Its restriction and embedding semantics therefore share that earlier model's unresolved graph correspondence. The Python example also influenced the selection of the Lean statement. Kernel checking certifies the stated executable-model proposition, while independent semantic verification remains required for the graph-theoretic interpretation.

The first 5,000-instance run checked 44,582 role swaps, 162,558 one-cut inequalities, and 4,194 pure completion optima. The other 806 generated completions failed the purity test and were excluded from the pure-elimination comparison. Root marks occurred in 22,291 local queries; 8,729 queries had leafless regions. These are finite counts, with exact pass criteria recorded before execution. They imply no universal correctness claim.

## Unrestricted target

A completion algorithm applies to an already-cut source forest. Entering that class by arbitrary cuts can remove every original optimum. An unrestricted improved base still requires a proved safe cover of refinements, an accounted construction size and cost, and a bound on the hardest local component. None is supplied here. The separate Whidden 2013 base-two reconciliation remains open; no novelty conclusion follows from this formal checkpoint.
