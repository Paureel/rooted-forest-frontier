# Frozen charge-route controls (2026-10-14, before proof code)

Source of exact instances: `../controls.json` (shared frozen target data only,
not checker code). All eight positives must reproduce every printed support,
owner, count, cost and toll exactly. Primary sentinel T1 is R1: parent 2,
children 1 and 1, parent cost 2, children cost 0 and 0, toll 2.
R5 must charge a parent-closed region owning a child root (child cost 0);
R6 must retain unused child root (left cost 2 and left root owner absent);
R8 must preserve three distinct indices although all four labels equal x
(left and right counts 2, parent cost 2). R2/R3/R4 check other transitions.

Numerical negatives: all five `wrong_numbers` and all three `corruptions`
from the shared frozen data must be detected, each clean twin must pass.
Duplicate and omitted enumerations, overlapping supports, wrong parent root
owner, and raw leafless child-root incursion must be detected by exactly
stated input checks. Empty list/null charges must be zero.

Lean controls, fixed before proof code:
- Positive closed charges on [0,1], L=(i=0), R=(i=1), parent owner none,
  child owners 0 and 1: charges (2,0,0); total child counts 2.
- Positive merge on [0], L=R=true, all owners 0: charges (0,0,0),
  total child counts 2 versus parent count 1 plus duplicate 1.
- Positive unused child root on [0,1,2], L=(i<2), R=(i=2),
  parent and left owners none, right owner 2: charges (3,2,0).
- Positive repeated-label survivor pattern on [0,1,2], L=(i≠2), R=(i≠1),
  parent and child owners 0: charges (2,1,1), total child counts 4.
- False goals: T1 parent charge 0; unused-root left charge 1;
  repeated-label pattern left live count 1; merge parent count equals
  unreduced child total. Each must fail specifically at `by decide` with
  a false-proposition diagnostic, while its clean twin compiles.
- Malformed-import failure is recorded separately and never counts as a
  proposition rejection.

No numerical fitting or approximate arithmetic; all comparisons are exact
integers/sets. Precision escalation and held-out fitted-point checks do not
apply. This producer's controls cannot confer fresh-review acceptance.
