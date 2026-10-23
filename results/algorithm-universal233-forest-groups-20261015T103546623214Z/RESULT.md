# Author forest-state grouping checkpoint

The grouped forward and reverse theorems compile for the original finite
`ForestState.agrees` definition. The status is author proof awaiting independent
nonauthor reconstruction and adversarial review. The complete algorithm,
runtime milestone, and all three main milestones remain OPEN. No novelty claim
is made.

A checked partition Q of the target labels groups whole current source trees.
`owned ss U` filters the literal current source list by leaf containment in U;
`localTarget T U` is the literal suppressed restriction of T. The forward
result takes any original agreement F to the local family `family U F` for
every U in Q. The reverse result concatenates any family G of local agreements.
Its cross-group hypothesis compares the actual minimal target embeddings of
individual current source trees in different groups. Source trees in the same
group may have overlapping target embeddings.

The reverse proof uses partition uniqueness to show that filtering the
concatenation to one original source tree returns exactly its own local
family, with literal order and multiplicity. It transports local target
embedding checks through actual restriction and suppression. For blocks from
different groups, it first recovers their current source owners and then uses
minimal-embedding monotonicity and current-source-piece clearance. It never
assumes clearance of whole original parent hulls.

The exact cost results prove

    sum_U (|G U| - |owned ss U|) = |concat_U G U| - |ss|.

The forward formula uses `G U = family U F` and gives `|F|-|ss|` on the right.
Each local valid forest has at least as many blocks as current source trees;
this justifies every natural subtraction before summing. The budget statements
hold for every natural q. The general theorems allow arbitrary natural labels,
source order, block order, and group order. The Option.none case with empty
sources and blocks is explicit; a checked partition never contains empty groups.

`retained_A_one_plus_Bforest` uses the literal source list `[a] ++ bs ++ cs`.
A supplied actual A agreement has additional cost one; any valid residual
agreement for bs and any completed cost-zero agreement for cs concatenate to
an original agreement with cost `1 + additionalCost bs FB`. The derived
ownership equations identify exactly `[a]`, bs, and cs as the three local
source lists. `PriorityClear` compares A with every B and C piece, and every
B piece with every C piece. It makes no pairwise-clear assumption within bs.
`retained_A_one_Bforest_no_C` covers an empty completed C by using the checked
two-group partition. The general theorem covers singleton and empty grouping.

The concrete retained A is `(0,(1,2))` against `((0,1),2)`, with local forest
`[[0,1],[2]]` and cost one. Its second block is leaf 2, reached in A by the
original path `[true,true]`. The B sources are `(3,5)` and `(4,6)` inside target
`((3,4),(5,6))`; their minimal target embeddings overlap. The singleton B
agreement costs two, and the combined agreement including completed leaf 7
costs three. `actual_A_any_residual` applies the universal concatenation theorem
to this actual A and to every valid residual B-forest agreement.

The controls were pinned and executed before the universal grouping proofs.
They check ordinary disjoint components, the retained bad A with overlapping
B pieces, incorrect cross-group clearance, none/empty and singleton states,
and permuted source/block order. Three deliberately false propositions were
rejected: concatenation without cross-clear; replacing the B forest by a free
whole-B tree; and charging the combined forest two instead of three. The
first compilation attempt used list indexing that required an unavailable
`Inhabited Tree` instance; the retained log records that elaboration failure.
The repaired controls use the same explicit source trees and expected values.
Postproof consumer controls separately apply the universal results.

`residual_query_lift` licenses a successful future query on the whole B forest
at q-1 when q is positive. Its hypothesis is the child-specific
`ResidualSolverContract solve (localTarget T B) bs (q-1)`. That contract asserts
soundness, the returned budget, and complete failure exactly when every valid
child forest exceeds the budget. No implementation, induction termination,
or recursive runtime theorem is provided. A positive own minimum alone does
not justify decreasing a query budget.

The source-level construction audit is in RUNTIME.md. The isolated replay
rebuilds all imported local modules from frozen original sources, inventories
every declaration by its actual module origin, restricts its axiom dependencies
to Lean's standard axioms, and executes false and corruption controls. The
canonical replay receipt and its measured counts are identified in the final
manifest. Those checks certify this author replay procedure; independent
mathematical acceptance remains pending.
