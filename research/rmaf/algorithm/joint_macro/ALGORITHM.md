# Total candidate A0 and its paid boundary

Date 2026-10-14. Complete algorithm / exactness / smaller exponent: OPEN.
This is a total design, with an exact finite fallback; it is not an accepted
new FPT bound. Mathematical source imports below are conditional until their
implementation/graph interfaces and required Lean proofs are supplied.

## State, priority and terminal convention

State is `(T, F, q, history)`. `T` is the current ordinary rooted binary tree;
`F` stores the explicit current forest topology and leaf blocks; `q` is the
number of further source cuts permitted. History stores component edge cuts,
singleton closures, the retained label and expansion of every contracted
common cherry, and any role swap. Initially `F=[Tprime]` and `q=k-1` for a
nonempty input. No rho label is added. Empty states need zero components;
singleton states need one component and no further cuts.

The specified **exact fallback** is `EdgeSearch(T,F,q)`: enumerate every
subset of at most `q` edges of the current forest; cut it, discard unlabeled
regions, suppress unary vertices, and form its leaf partition. Accept only
if equal rooted restrictions and pairwise vertex-disjoint minimal spans hold
in `T` and in the ORIGINAL component topology of `F`. Return the first
partition passing that polynomial validity test, with its explicit cut
history; if all subsets fail return failure. This is an algorithmic cut
enumeration, not an optimum oracle. It makes the specification total when a
source rule/implementation interface is unavailable. It costs
`poly(n) * sum_{j=0}^q binom(m,j)`, where `m` is the source forest edge count;
this is generally `n^O(q)`, not a claimed FPT fallback.

Candidate priorities, with every failure/unsupported interface sent to that
escape instead of an undefined action:

1. Reject malformed inputs (nonbinary nodes, duplicate/missing labels).
   Return failure for negative further-cut budget. Delete singleton forest
   components and close their expanded blocks; suppress unary vertices;
   contract common cherries only when pendant in both `T` and one `F`
   component. Repeat to a fixed point, recording all actions.
2. If the current forest itself passes the agreement-partition test, return
   it. If `q=0` and it does not, return failure. This covers empty/singleton
   and identical-tree boundaries without a root convention change.
3. On a tree-tree call, test *all* cherries in both orientations. Apply the
   first applicable Figure16 rule: Whidden t1; Whidden t>=3; rule4; rule5;
   hard Whidden t2. Common cherries must already be absent. Source v2
   Figure16, p24 and rules/lemmas cited below specify their covers.
4. Hard t2 emits the two endpoint-isolation children at paid decrease1 each
   and the child cutting both actual pendant edges at paid decrease2. Only
   on that latter child, tidy, then apply rules6/7 before A0. For a connected
   three-parent overlap chain, rule6's isolated-third-component premise is
   false and rule7 applies precisely when all three parents are homeomorphic.
5. If precisely three live parents share a T-edge, apply `Joint3` below.
   If precisely three form an edge-overlap chain with vertex-disjoint
   endpoints, apply `JointChain4` below. Otherwise execute the attributed
   original SPLIT/decompose scaffold; unavailable imported implementations
   use `EdgeSearch`.
6. After a macro, repeat tidying and agreement checks, apply pairwise SPLIT
   to exhaustion for remaining overlaps, then the disjoint decomposition
   query below. Remaining general tree-tree subinstances resume at1.

No optimum number or optimum partition is queried in any candidate step.
The `exact(...)` calls in development instruments are falsifiers only.

## Explicit local covers

`Core(U,Y)` is the source Lemma1 construction (pp7–8): choose an
edge separating Y from its complement if one exists; otherwise choose a
degree3 node with a pure-Y twig, pure-complement twig and mixed twig, and
branch on deleting either pure twig edge. Recurse on the remaining mixed
source tree. Retain original source-edge identities; emitting a core child
costs the number of distinct deleted edges. Coverage means **partition
refinement**, not literal containment of edge sets.

`Joint3(T,[A,B,C],e,q)` has survivors0,1,2. For each survivor, lazily emit the
Cartesian product of cores splitting both other SOURCE parents according to
the two sides of e. Emit the union of source cuts, with paid cost the sum;
recurse with `q-paid`. Parents are different forest components, so cuts in
their source graphs are disjoint. A branch with paid cost exceeding budget
is discarded while generating, not after constructing an unbounded core.
If no final block crosses e, any survivor is allowed; if a block crosses e,
its unique source parent is the survivor.

`JointChain4` chooses `e` in AB and `f` in BC by a fixed polynomial
description of the state (first address pair is the total default). It emits
the four ownership choices: `(A,B)`, `(A,C)`, `(B,B)`, `(B,C)`. Their splitting
constraints respectively are `B@e+C@f`, `B@e+B@f`, `A@e+C@f`, `A@e+B@f`.
For two constraints on B, split current B pieces sequentially; pieces not
crossing the next boundary cost zero. Every split carries a stage tree,
actual stage cut edges, resulting blocks and paid cost. Preserve those
stages so suppression does not turn an address into an invented source cut.
Identical partitions may be deduplicated. A finer paid child may be removed
only when an emitted coarser partition dominates it by refinement and cost.

Choosing the cheapest edge pair by fully enumerating unbounded cores is
**not** licensed as polynomial preprocessing. The development instrument
does enumerate its tiny measured fixtures; its timing is not a universal
generation bound. A production implementation must use paid budget-pruned
generation and account for every attempted pair; such an implementation is
OPEN. The specified first-pair rule remains total without this optimization.

## Disjoint query and reconstruction

For vertex-disjoint component embeddings, first try all at most1-edge local
cuts on each component pair; record its exact minimum `r_i` if0 or1, otherwise
record failure and lower bound2. If all resolve, unite their forests. For
each unresolved i, call the main solver on its tree pair with budget
`q - sum_{j!=i} lower_bound_j`; negative budget fails. Sum returned minima,
fail if total exceeds q, and unite witnesses. This is the source recursion
rule, pp9–10. One unresolved query is charged separately; it does not receive
a fictitious lower bound for its own cuts.

Reverse stage histories: restore suppressed vertices as paths if a cut
witness needs original edge IDs; expand contracted labels into the saved
pendant common cherries; reinsert closed singleton blocks; reverse any role
swap with a realized forest partition, not an unproved graph correspondence.
At every externally returned witness, validate the expanded partition on the
original input trees and check its component count against the initial budget.
Failed validation returns to `EdgeSearch`, never an accepted answer.

## Charged recurrence and its failure

If the source core's coverage and base2 mass theorem are admitted, at any
c>=2, each nontrivial core has mass <=1/c: every emitted cut has size>=1,
so `c^-d <= (2/c) * 2^-d`. Independence of source components makes two core
masses multiply. Three survivor products have residual mass <=3/c², hence
full hard vector `(1,1,4,4,4)`, exact mass
`921759400/949132107 <1` at c=231/100.

That common-edge gain is useful at its named call site only. The simplest
four-choice chain cover does not universally have the same mass. The
smallest eligible refuter measured within our pinned deletion family has
ten leaves and *every* overlap-edge pair emits four distinct paid2 children.
Full vector `(1,1,4,4,4,4)`, exact mass
`2865278200/2847396321 >1` at c=231/100. One child is already a valid residual
forest, so no uniform “one further cut per child” charge is available.

The remaining Figure16 classes also must be charged. Source t>=3 and rule4
are below c; rule5's vector `(1,2,2,2)` passes c. Other overlap cases in
Lemma16 still use residual `(1,2,2)` unless separately improved; their full
`(1,1,3,4,4)` has mass `2896278200/2847396321 >1`. Thus source fallback
retains the audited2.3391 benchmark, and exact escape can be slower still.
This candidate establishes **no smaller overall exponent**.

For t=1 disjoint queries with p unresolved components, retain every
`p T(q-2(p-1))` term for p>=2 and its actual polynomial pretests. For p=1
charge `T(q-L)` with L the measured/proved lower bounds of the OTHER
components; L may be0. Precut, local query, contraction, validation and
reconstruction work must be polynomial per generated search node. The lazy
core's paid internal branches also consume budget; pruned dead branches
cannot be omitted from the time bound. These generation interfaces are OPEN.

## Universal obligation and import trace

| Consuming call | Exact required statement | Status |
|---|---|---|
| Joint3 survivor selection | Distinct final forest spans cannot both cross the same original T-edge; final block maps to one current source parent | OPEN graph/state interface |
| Each source Core | Every refining monochromatic partition refines an emitted core child; size equals paid cuts after suppression | Retrieved Lemma1, pp7–8; OPEN Lean/executable interface |
| Product of two cores | Refinements compose and cuts from distinct source components have additive cost; rooted restrictions/history transport correctly | Abstract conditional cover compiled; concrete interface OPEN |
| Chain4 ownership | For each overlap edge at least one source parent avoids it; sequential core refinement covers both boundaries | Abstract four-way implication compiled; graph/core correspondence OPEN |
| Whidden and rules4/5 | Source exact covers at printed hypotheses; both-orientation priority checks and symmetric witness transport | Retrieved pp6,17–22, Figure16; full formal import OPEN |
| Rules6/7 | Exact source hypotheses, edge realization and returned minimum forest; no pending degree-two/DP interface assumed | Retrieved pp23–24; OPEN consumer proof |
| Pairwise SPLIT/decomposition | Shared-edge or vertex-disjoint premise; all queries and cut histories paid | Retrieved pp9–10; OPEN formal import |
| Exact escape | Every rooted agreement forest is realizable by source-edge cuts; enumeration/validation correspondence | Direct design obligation, OPEN Lean theorem |
| Termination | Each paid rule decreases q; tidying decreases live labels; decomposition reduces to fewer source components; no zero-cost cycle | OPEN formal measure |
| Smaller base | Every hard class has target mass, all generation/query overhead charged | REFUTED for topology-free Chain4 at c=231/100; replacement needed |

No degree-two, pure-bridge or compatible/triple pending interface is imported.
The Lean files prove only their printed conditional implications and exact
integer inequalities; they do not close any graph or rooted-MAF obligation.
