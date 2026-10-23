# GLOBAL-CB4 — explicit paid guarded frontier

Frozen before CB4 tests, 2026-10-15. No new alpha/theta claim. This changes
the full-certificate proposal into an actual guarded partial-certificate
generator, still using GLOBAL original-edge conflict constraints. Preserve
CB1-CB3 and their exact obstructions.

At each original precut prefix C, compute its full original source components.
Prune if any is unlabeled or |C|>b. Test terminal class directly: all target
hull overlaps degree2 in both hulls, or every incompatible component has
exactly3 leaves. Construct a local agreement witness for every component
without an optimizer: use the whole component when compatible; otherwise
select disjoint source-and-target pair paths greedily in original-label
order and leave other labels singleton. Check each local witness directly.
Assign unused original source vertices to its connected block supports until
all are assigned; boundary edges give exactly pieces-1 local original cuts.
Emit the prefix only if every local witness costs<=floor(b/2), the terminal
predicate holds, and the literal source/cost/witness certificate verifies.
Stop that branch after emission.

If no guard passes, run the CB3 structural closure/row compilation and recurse
on every retained child within the remaining ORIGINAL cut budget. Include
all forced original edges. Do not reuse a cache across different C masks:
terminal geometry and local witnesses depend on the actual original forest.
A visited key must include C, exact residual rows and remaining budget.
Do not call a local distance, optimum, partition or packing oracle.

Conditional coverage uses C1/C4: each state retains a full original minimum
transversal path. Any prefix of a normalized original optimum has no empty
component. A guarded stop on that path preserves that original optimum;
otherwise its remaining minimum branch survives cost domination. At worst
its full optimum is all-compatible with local cost0, so it must stop by b.
Every emitted output satisfies the guards by explicit original graph checks.
The generator may emit nonoptimal prefixes; it must emit at least one that
preserves an ORIGINAL optimum whenever opt<=b. Completion still consumes
only the separately proved terminal solvers; no completion interface is
silently discharged here.

All geometry, witness construction, rejected outputs and search states are
paid. The generic count remains O*(d^b), potentially n^b. The required
alpha5/4 or prelicensed3/2 state/frontier bound remains OPEN. CB1's full-search
lower family and CB3's one-row mass obstruction cannot automatically be
transferred to this earlier guarded stopping rule.

Controls before scoring: zero/empty/singleton, compatible pair, incompatible
triple witness cost1, and pure crossed-pair hulls; original local cut witness
cost must equal pieces-1 and all components retain labels. Corrupt local cost,
source vertices and target support, with clean twins. Then use the same nine
literal ordinary fixtures and test all emitted certificates; partition
oracles are scoring only. Check existential original-optimum survival at
b=opt and b=opt+2, with all scoring oracles disabled during generation.
