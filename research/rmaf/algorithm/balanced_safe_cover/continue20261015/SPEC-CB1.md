# GLOBAL-CB1 — factorized original-conflict optimization

Frozen before new construction tests, 2026-10-15. This is an executable paid
proposal, not an established unrestricted faster algorithm. It preserves the
original alpha=5/4 and prelicensed alpha=3/2, theta=1/2 registrations.

## Actual candidate

Build the original-source-edge conflict family H specified by conflict/PROOF.md
C1. Delete duplicate rows and proper row supersets (a hit of every minimal row
hits every original row). Factor the bipartite incidence graph into connected
components. Their edge universes are disjoint, so optimize each factor once;
do not take a Cartesian product of optimum witnesses.

For a factor and nonnegative remaining budget t, bounded SEARCH does:

1. If no row remains, return the selected original edge set.
2. If t=0 while a row remains, return failure.
3. On the remaining rows, retain one canonical original edge from each
   inclusion-maximal nonempty incidence column, exactly C4.
4. Replace every row by its retained representatives, deduplicate and remove
   proper supersets. Choose the row with fewest edges, ties by integer mask.
5. In increasing original-edge order, select each edge e of that row in turn,
   delete all rows hit by e, and recurse at t-1. Return the first success;
   return failure only if every branch fails.

Run SEARCH at budgets 0,1,... for each factor up to the unspent global budget.
The first successful budget is that factor's exact minimum. Sum its cost,
subtract it from the unspent budget, and retain one witness. If any factor
fails at every available budget, return a valid global budget failure. If all
succeed, unite their witnesses and check the original cut graph, rooted
restrictions, and unsuppressed target supports. Emit one full agreement forest.

This has no optimum oracle, no local distance optimizer, no packing optimizer,
and no uncharged recognition. A full optimum output is all-compatible and has
original unmarked tau=0. On every b>=opt it must return an ORIGINAL optimum,
not merely the first feasible witness at b. Empty/identical inputs cost zero.
All cuts are original edges. Optimality plus normalization implies there are
no empty source components and r+1 leaf-bearing components for r cuts.

## Explicit imports and costs

C1's actual source-model characterization and normalization remain handwritten
claims pending fresh review. Generic dominance and independent factorization
are not substitutes for that source correspondence. Every returned certificate
is also polynomially checked directly from the original trees.

Let d be the largest chosen-row cardinality in any executed bounded search.
Each fixed-budget search has depth at most t and at most 1+d+...+d^t nodes;
polynomial work per node includes column reduction, all rejected branches,
source conflict construction, and output validation. Iterative deepening and
factor count cost only polynomial factors. Thus a branch cap d supplies
O*(d^b), not O*((3/2)^b) without a structural theorem. The cap is descriptive
for completed executions; it is not a free production recognition oracle.
No alpha=3/2 universal bound is asserted.

A restricted d<=2 proposal is preregistered as alpha=2, theta=0 before tests:
its exact arithmetic is 2<23391/10000. It is an optimization subroutine for
inputs whose complete search trees have that cap, not a universal graph fact.
This does not change the global safe-cover target.

## What an adversary is asked to determine

Find exact ordinary source pairs or a proved infinite source family forcing
this ACTUAL factorized algorithm above the licensed (3/2)^b generation rate.
A finite node count alone cannot refute O*(alpha^b). Disconnected gadget
products must be factored before counting, and a lower bound for enumerating
all optima does not refute this one-witness algorithm. An abstract hypergraph
is only an abstract control until realized by actual source/target trees.
Record ordinary/reduced eligibility separately. A certified kill rejects
this candidate's runtime only, not existence of a different guarded cover.
If no exponential lower family is obtained, report the exact missing connected
factor bound; do not call a finite NO-FIRE a universal proof.

## Frozen controls

Abstract controls (edge indices start at zero):

- H=[], M=0: optimum0, one empty solution.
- H=[{0,1,2,3}], M=4: one maximal column, optimum1.
- H=[{0,1},{1,2},{0,2}], M=3: optimum2, three maximal columns.
- H=[{0},{1}], M=2: two factors, optimum2. At b=1 fail.
- Two disjoint triangle factors on edges0..2 and3..5: optimum4, two factors.
- H=[{0,1},{0}], M=2: optimum1, row supersets removed.

Ordinary fixtures with literal old optima (reproduction, not independent):
empty0, singleton0, identical cherry0; crossed quartet optimum2; equal-halves
witness optimum1; quotient-star witness optimum3; matched-sector m1 optimum0,
m2 optimum2, m3 optimum3. Preserve exact input trees in CONTROLS-CB1.json.
Every clean certificate must pass full source-edge/cost/partition verification.
For every nonempty fixture, +1 cut accounting must fail. Changing a valid
certificate's labels or target support must fail. False global bound 3/2>=2
must be rejected. Abstract expected optima and component counts are frozen
by direct construction before implementation.

## Lineage / tool consultation

Read bootloops/tools/README.md, algorithm/README.md, conflict/README.md and
existing exact_conflicts.py, dominance_checks.py, quotient/SlowCover.py.
They provide polynomial primitives and exhaustive test oracles but no
factorized conflict optimization routine. Extend by a new one-shot problem
solver and reuse original primitives; preserve frozen tools and receipts.
New tests use the retained partition oracle only as production-side scoring;
a fresh nonauthor child must freeze its instrument before reading this solver.
