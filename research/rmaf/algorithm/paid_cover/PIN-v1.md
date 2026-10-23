# Candidate B1: clear realizable overlap cores, then complete exactly

Frozen before this route's solver/control/pilot runs, 2026-10-14.
Theory-finding candidate; no universal or exponent claim is accepted.

## Total state and algorithm

Input `(T, F, q)`, ordinary rooted binary `T` and a list `F` of nonempty
source-component trees partitioning the target labels. `q` is an integer
remaining cut budget. No rho or implicit completed-component deletion.

1. Reject malformed trees, duplicate/missing labels, and negative budget.
   Empty target with empty forest returns the empty witness. A singleton
   returns its sole block. A directly valid current forest returns it.
2. Find the first target vertex `v` shared by two or more source-component
   target spans, with degree three in at least one of those spans. Admit the
   core only when **every touching source component is compatible with its
   target restriction**. If none is admitted, go to step 4.
3. For each touching color `j` retained at `v`, split every other touching
   color into the nonempty leaf regions of its target span minus `v`.
   For each split, enumerate source cut sets of size `r_i-1` (at most two)
   and require an exact matching source partition; abort this acceleration
   and use step 4 if the certificate is absent. Emit one explicit child per
   distinct resulting forest partition. Charge `d_j=sum_(i != j)(r_i-1)`;
   discard `d_j>q`; recurse with `q-d_j`. Reconstruct by concatenating the
   recorded source cut histories and returning the child's full partition.
   If every emitted child fails, return infeasible.
4. Classify compatible/triple and pure-bridge membership for a call-site
   ledger. The conditional terminal libraries are **disabled in v1** because
   their graph interfaces are open. Execute the exact fallback in step 5.
5. Enumerate every cut set of size `0..min(q,E)` from the disjoint union of
   current source edges, where `E=2n-2m`. Derive labelled cut regions, discard
   leafless regions, suppress via source restriction, and test rooted
   restriction equality and target/source vertex disjointness. Return the
   first valid cut forest plus the actual source-edge cut list; otherwise
   return infeasible. This is explicit finite search, not a test optimum
   oracle. Iterative budgets `0..n-1` solve the initial optimization problem.

## Proposed payoff and rejection criteria

For a compatible core, `r_i` is its degree at `v`, hence 2 or 3. The
candidate proposes one branch per possible occupying color with costs above.
At least one color has weight 2. For two colors the least paid vector is
`(1,2)`; its mass at `231/100` is `33100/53361 < 1`. For larger cores the
claimed bound requires its own general proof; binary arithmetic is not an
m-color certificate. Precise generation work is charged: `O(m E^2 poly(n))`
per core, at most `m` children, and each recursive branch decreases `q`.

Fallback work is `O(poly(n) sum_(d=0)^min(q,E) binom(E,d))`, with witness
checking and reconstruction included. No bound with a constant base below
2.3391 is claimed for this fallback.

If a pure-bridge local solver were enabled, each component gets an exact
joint-mark query. The first query's additional-cut budget is at most `q`;
the role-swap target budget is at most `q+r-1` for `r` nonempty marked
regions, per `pure_bridge/FORMAL.md`, G5-G7. Query budgets are not silently
replaced by the number of initial source components. In particular, the
initial one-color state has `r=1`, no mark, zero paid cuts, and a local query
identical to the original `(T,T',q)`. This is the first falsification target.

Reject the improved-algorithm candidate if an outside-triple initial state
emits no paid cover and its only local query is the unchanged original
problem. Retain the smallest measured input by leaf count (then lexicographic
canonical input) in the frozen tested family. Also reject any extrapolation
of `r_i-1` cuts to incompatible components if a split has intersecting source
spans or needs more cuts.

## Frozen controls

All controls pass through the same executable entry point as the pilot.

- Empty: `(None, [], 0)` succeeds with zero blocks/cuts.
- Singleton: `(0, [0], 0)` succeeds with one block/zero cuts.
- Identical rooted triple `((0,1),2)` at zero budget succeeds.
- Conflicting rooted triple target `((0,1),2)`, source `((0,2),1)` fails
  at zero budget and succeeds at one with two blocks. Wrong full block
  rejected; clean two-block twin accepted.
- Target `((0,1),(2,3))`, sources `(0,2),(1,3)`: one further cut succeeds
  with three blocks; zero fails. Overlapping unsplit pairs rejected.
- Duplicate tree label, duplicate forest label, missing target label,
  empty forest component, and negative budget rejected.
- Suppression: `((0,1),(2,3))` restricted to `{0,2,3}` equals `(0,(2,3))`.
- Degree-three mark/control: in identical `((0,1),2)`, removing vertex
  joining `0,1` creates three leaf regions and requires two cuts; the false
  one-cut certificate must fail.
- Source realization corruption: target quartet `((0,1),(2,3))`, source
  `((0,2),(1,3))`; target-root regions `{0,1}|{2,3}` cannot be realized by
  one source cut, since their source spans overlap. Clean source twin equal
  to target realizes them with one cut.
- Mass comparator: `(1,2)` at `231/100` is `33100/53361`; adding an
  unpaid same-budget branch adds 1 and must reject a strict-decrease claim.
- Deliberately wrong returned block count and missing-branch comparator
  must fire on the conflicting rooted triple's literal valid two-block
  witness, with their clean twins accepted.

## Freshness and proof boundary

Read X0 report and supporting library/code guides during design; their
values are development references, permanently burned for certification
of this candidate. The existing graph primitive implementation is wrapped
for development; no separate-author graph certification is claimed. A
nonauthor must rebuild the accepted candidate later, if any. Every universal
graph obligation is OPEN until Lean proof and axiom audit, and fresh review.
