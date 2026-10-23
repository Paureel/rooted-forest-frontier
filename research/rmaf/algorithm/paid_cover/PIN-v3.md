# B3: full minimal terminal cover, exact total fallback

Frozen after the five-leaf B2 fire and before the B3 run, 2026-10-14.
No improved exponential bound is claimed.

## Total generator, solver, reconstruction

Use the same fully specified input convention and explicit source cut-set
generation as B2. Enumerate **all** cut sets with `d<=q` and retain every
compatible/triple labelled forest, with its actual cut certificate and
charge `d = number_of_child_components-number_of_initial_components`.
Deduplicate by label partition. Remove a retained state P if another
retained state R strictly coarsens P (every P block is contained in some R
block). The remaining family is the full minimal terminal cover.

For each retained state P, invoke the explicit budgeted completion with
budget `q-d(P)`. Validate each returned partition against both original
graphs. Reconstruct its original source cuts by extending the disjoint
minimal spans with the deterministic multi-source BFS from B1. Return
the first feasible result. If none is feasible, execute the original-state
exact cut-set fallback. The fallback gives a total action even while the
universal cover/suppression proof is open; every fallback call is charged.
For optimization, test budgets 0 through n-1 and return the first witness.

No optimum oracle enters the algorithm or the cover selection. The
development harness separately measures the parent optimum to test it.

## Coverage argument and exact debt

Candidate argument: every feasible agreement forest has compatible source
components, so its source cut partition appears in the retained all-terminal
family. In a finite family, descend through strict coarsenings until reaching
a minimal terminal partition that it refines. Such a partition has at most
as many paid cuts, and the remaining cuts fit the residual budget. Restriction
and suppression must preserve the final source embeddings. These are the
exact universal obligations to formalize; finite checks do not close them.

There is no recursive branching in the generator. Every cut-set size and
combination loop is finite; every coarsening scan is finite; every budgeted
completion is the explicit finite fallback. BFS reconstructs each vertex
once and checks all original source cut regions before accepting.

## Paid cost

Let `E=2n-2m`, `H=sum_(d=0)^min(q,E) binom(E,d)`, `M` be all distinct
terminal states before coarsening, and `N` the retained states. Generation
uses `H` cut-set/class tests, polynomial per test. Coarsening costs
`O(M^2 poly(n))`; no duplicate or discarded state is free. For retained
state i, its exact query budget is `q-d_i`. The hypothetical triple-library
call would cost `O(n*m_i)` **conditional on G1-G3**; the actual executable
cost is `sum_(e=0)^(q-d_i) binom(E_i,e) poly(n)`. Original fallback adds
`H poly(n)` when used. Reconstruction costs polynomial time per accepted
witness. A budget loop adds the sum of these costs for q=0..k-1.

The target mass check is `sum_i (100/231)^d_i`, reported exactly. Failing
that check refutes this sufficient paid-recurrence certificate; a one-level
terminal macro with mass >1 does not by itself refute every possible global
charging argument. The enumeration bound remains explicitly non-FPT in this
route and therefore supplies no O*(c^k) claim for any fixed c.

## Frozen controls and measured run

Replay B1 controls and the B2 seven frontier controls first. On the B1
quartet at q=2, the minimal family must contain exactly the five one-cut
states; its paid mass is 500/231. On the B2 five-leaf fire at q=2, B3 must
contain a state coarsening the literal optimum `{0,1,4}|{2}|{3}`, and recover
the two-cut witness without invoking original fallback. Deleting every
cover state coarsening that literal optimum must make the literal coverage
check fail. A complete-family clean twin must pass.

No enlargement beyond these retained fixtures is accepted without another
measured pilot. Their outcomes remain development evidence because the
same graph implementation and previously contacted inputs are used.
