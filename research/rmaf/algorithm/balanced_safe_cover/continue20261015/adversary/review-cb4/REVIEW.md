# CB4 bounded nonauthor review

Verdict: all 18 frozen-input covers and all 24 emitted guarded certificates
pass independent finite verification. Every cover preserves at least one
original optimum. The source-cut realization, local original supports,
terminal predicate, explicit half-budget witnesses, and actual unmarked local
distances all check. No counterexample to existential coverage or the stated
prefix-dominance substitution was found. Alpha, universal C1/source
correspondence, and the terminal-completion interfaces remain open; no Lean
closure or runtime improvement is claimed.

The coverage argument needs an existential path invariant, not a claim that
every reachable state preserves an original optimum. The latter reading of
SPEC-CB4 lines 28-29 is false on two actual compiled states of the frozen
six-leaf input. Their exact witnesses are below. This quantifier correction
does not change the algorithm or the confirmed existential cover property.

## Frozen independent checks

The review design and positive/negative controls were frozen before any new
review execution. The checker reuses the frozen X0 instrument
`adversary/independent_cb1.py`, hash
3e5ef9bb655ee5adb055c016fe19a311331ea99d8637af85f1ac65d7f04dfc83,
for literal trees, BFS paths, recursive restrictions and partition enumeration.
No production guard, support, component or witness verifier is reused.
Parent edge/vertex numbering is metadata: a clade-based map to the independent
literal trees must pass a complete rooted vertex/edge/label isomorphism check
before any certificate is interpreted. The shared mathematical tree model
and canonical identity metadata are explicit lineage contacts.

Five clean guard controls passed. Four deliberately corrupted twins were
rejected: local cost, local target support, full source vertices, and a false
half-budget claim. The coverage checker also distinguished two valid nonempty
guards of the equal-halves control at budget 1. Precut clade {c,d} preserves no
original optimum, while pendant b preserves one. This tests the coverage
comparison separately from certificate validity; a valid guard alone is
insufficient to certify the existential statement.

The unchanged review instrument then generated at b=opt and b=opt+2 for all
nine frozen inputs, with production partitions, oracle, packing and exact_row
functions replaced by raising functions during generation. Scoring ran only
after restoration. All generation outputs and statistics matched the pinned
CB4 receipt exactly. The cover run checked 24 certificates in
0.042240750000019034 seconds; the preceding control gate took
0.0011992500003543682 seconds. No broad census or long run was launched.

## Certificate validity and original cut realization

For each certificate the checker independently reconstructs the complete
original source cut graph. Every component retains labels, its literal full
source vertices and labels agree, and the distinct precut count is within b.
Nonempty inputs have r+1 leaf-bearing components for r cuts. Each stored
source restriction and target hull matches independent computation.

Every local witness partitions exactly its component labels. Its block
restrictions agree, and its original unsuppressed source supports are
pairwise disjoint inside the full actual component; target supports are
pairwise disjoint within that local witness. Each submitted target support
matches the original target graph. Local cuts are distinct original internal
edges, disjoint from precuts. Removing them inside the full source component
produces exactly the submitted blocks, with no unlabeled component. Local
cost equals both the number of original local edges and pieces-1.

The witness construction's connected-support expansion is valid. Initially
each nonempty block owns its connected source hull, and the hulls are
disjoint. Assigning an unowned adjacent vertex to an owner's group preserves
connectivity. Every labeled leaf is already in its own block's hull, so
assignment cannot move a label to another block. Expansion reaches all
vertices because the full source component is connected. Contracting the
resulting q connected groups in that tree gives a tree on q vertices, hence
exactly q-1 original boundary edges. Those boundaries realize the literal
block partition with no empty group. This is a source-model proof review,
not a new formalization.

The checker recalculates target-hull intersection degrees and compatible-or-
three membership directly. Every emitted prefix satisfies at least one of
the two implemented terminal predicates, and its stored flags/class agree.
These finite predicate checks do not discharge the separately open
pure-bridge or compatible/triple completion theorem interfaces.

All explicit local costs are at most floor(b/2). Independent exhaustive
local partition scoring gives actual original unmarked distances no greater
than those costs. The maximum actual tau is 2 in these covers. For example,
the crossed quartet at budget 4 is emitted uncut, has actual local distance 2,
and satisfies the half-budget bound exactly. At budget 2 it is cut into three
compatible components, with actual local distances all 0. The six-leaf
quotient-star budget 5 outputs have actual tau=2; their budget 3 outputs have
actual tau=0. Local scoring is test-only and was unavailable during generation.

## Prefix-dominance proof at early guarded stopping

Assume C1's source correspondence and the stated C4 replacements. At a state
known to have some full original minimum cutset K extending its current
prefix C, choose such a K represented in the current residual quotient.
The residual optimum is |K|-|C|: anything smaller, united with C, would
contradict original optimality. Column replacement and singleton forcing can
change K but preserve the existence of a minimum extension of C. Every
remaining row contains some edge of a represented minimum, so at least one
raw child has a full minimum extension after its forced closure.

Let that raw child's original prefix be P_j, its explicit cost delta_j, and
let W be its residual witness with

    K = C union P_j union W,
    |K| = opt,
    |P_j| = delta_j.

If retained child i dominates j, its cost satisfies delta_i<=delta_j and
every transversal of residual j hits residual i. Thus the same W satisfies
residual i, and

    K' = C union P_i union W

hits all original conflicts. Original rows hit by the branch/forced prefix
remain hit; all other projected rows are hit by W; projection/subsumption
only replaced rows by contained rows. Its cardinality is at most opt.
C1 and original optimality force equality, so K' is another original minimum
cutset extending C union P_i. Duplicate overlaps could only lower that
cardinality and therefore cannot invalidate the upper-bound argument.
The proof preserves some minimum, rather than a fixed preselected minimum.

A normalized original minimum has no unlabeled source component, and neither
does any subset of it. Therefore pruning empty-component prefixes cannot
remove this surviving path. If its current C passes the guard, the original
minimum partition induced by K' refines that actual source forest, so early
emission already gives the required survivor. If the guard fails, continue
through a retained minimum child as above. Prefix size strictly increases,
and at its full minimum the components themselves form an agreement forest;
each is compatible and has an explicit zero-cost witness. The guard must
therefore stop by opt<=b. Greedy witnesses may miss an earlier guard, but
cannot block this zero-cost endpoint.

The visited key at guarded_frontier.py:136 includes (rows,C,left), as required.
Actual geometry and local witnesses depend on C; equal residual rows alone
would not justify merging distinct forests. With C strictly increasing on
recursive edges, marking a state visited cannot create a cycle that hides
its unfinished ancestor. An already completed identical state has identical
guard geometry and descendant choices.

The bounded trace independently enumerated actual original minimum cutsets
for the six frozen runs that compiled a row. It inspected 15 compiled nodes,
13 of which had original-minimum extensions. Across 106 raw-child/minimum
witness pairs, all 108 retained substitutions were actual original optima
under direct original cut-graph and rooted-support checks. All 85 full
original minimum cutsets tested by this trace passed the guard with tau=0.
These are finite checks of the reviewed invariant, not its universal formal
proof.

## Exact quantifier witnesses

At quotient-star budget 3, the generator actually compiles states with these
original source precuts:

| Prefix mask | Edges | Source leaf partition | Original optimum | Minimum total cuts refining prefix |
|---|---|---|---:|---:|
|65|0,6|{a,b,d,e}, {c}, {f}|3|4|
|257|0,8|{a}, {b,c,d,e}, {f}|3|4|

Independent enumeration of all label partitions gives the last column and
retains explicit optimum refining partitions. Thus not every reachable state
has a full original-minimum continuation. Both prefixes are harmless extra
search states; the generated cover still preserves original optima elsewhere.
SPEC-CB4 lines 28-29 should say: from any state that extends some original
optimum, the operations preserve at least one such continuation or emit a
guard containing one. Lines 34-35 already state the correct global existential
requirement. Preserve the frozen spec and record a clarification rather than
silently replacing its wording.

## Prior document corrections

The corrected RESULT uses solve(S,T,max(0,n-1)) and explicitly accounts for
empty cost0. Its one-row discussion identifies mass<=1 as a proof obligation
and says the executable search continues above1. The CB2 clarification
addendum states the implemented first-nonsingleton stopping rule and preserves
the frozen pin/code. Those substantive prior findings are resolved. Several
minor numeric joins remain, such as at most2n-2, optimum is 3 and costing1;
they do not affect this scientific verdict. The CB1 infinite-family argument
and earlier compiler/axiom release review were not recertified.

## Remaining scope

Finite original certificate validity and original-optimum cover survival are
confirmed on the stated inputs/budgets. Conditional source-model coverage has
a coherent existential proof once its state quantifier is stated correctly.
Universal C1/normalization, complete terminal-solver correspondence, guarded
frontier alpha size/time, and source-bound Lean verification remain open.
No exact counterexample to that corrected existential coverage argument was
found. No parent file or original receipt was edited by this review.
