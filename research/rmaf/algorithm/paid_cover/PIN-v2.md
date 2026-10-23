# Candidate B2: minimum-paid terminal frontier

Frozen after B1 failure, before B2 controls/pilot/search, 2026-10-14.

This changes the organizing principle from overlap clearing to source
precuts that admit compatible/triple completion. The measured B1 quartet
is a development fixture. No input used here may later certify this design.

## Explicit generator and total action

Enumerate all source edge cut sets by increasing size d. Form every labelled
cut partition and suppress its component trees by rooted restriction. Test
that each resulting component is target-compatible or has exactly three
labels. Stop at the first d for which any state passes, deduplicate by the
label partition, and emit every passing state at that d. Charge all d cuts
and all enumerated cut sets, including failed class tests and duplicates.

Run an exact budgeted completion on each child with q-d, retaining its
original source cut list and returning its final forest reconstruction.
In the experimental complete executable the library is disabled pending
G1-G3, so completion uses explicit budgeted cut enumeration. If every child
fails, the **total** solver executes the B1 full original-state fallback;
that unpaid fallback is charged and prevents any improved exponent claim.
The acceleration-only cover claim says the fallback is unnecessary. That
claim is the object to falsify, not an assumption of the total solver.

Generation costs `sum_(e=0)^d binom(E,e) poly(n)` before deduplication;
N retained children each pay d. Conditional polynomial terminal completion
would give paid mass `N*(100/231)^d`. Exact executable fallback completion
costs at most `N sum_(e=0)^(q-d) binom(E-d,e) poly(n)` plus original fallback.
No optimum oracle determines d or chooses the children.

## Frozen controls and search

Before search: the B1 27-control battery must replay without changing its
original receipts. The identical triple has one frontier state at d=0.
The conflicting quartet B1 fixture has five distinct first frontier states
at d=1 (four singleton isolates and the two-cherry split). The latter has
paid mass `500/231 > 1`; a false acceptance must fire. A deliberately
deleted quartet frontier must be detected by its literal cut partition,
with the complete family accepted.

The search compares the acceleration-only minimum frontier against explicit
original-source budgeted cut search. FAIL means a parent feasible at exact
budget q has no feasible completion in any retained minimum-paid child.
Retain the parent, all frontier partitions and actual cut edges, q and d,
the literal surviving parent witness, and each child's measured optimum.

Pilot: first 20 shape-quotient tree pairs, sizes 4 through 6, in deterministic
tree enumeration order. Measure before expansion. Bounded search: all
shape-quotient pairs through six leaves, stopping at the first failure and
then reducing leaf count in the searched family. If no failure occurs,
report the denominator and finite NO-FIRE; do not claim universal safety.

No newly invented statistical threshold is used: all comparisons are exact
integer cut counts and exact rational mass.
