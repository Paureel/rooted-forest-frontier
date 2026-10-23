# CB4 bounded nonauthor review design v1

Frozen before new review execution. Completed SPEC-CB4, guarded_frontier.py
and the production receipt were read. No new alpha/theta claim is tested.
The independent instrument lineage is adversary/independent_cb1.py, SHA256
3e5ef9bb655ee5adb055c016fe19a311331ea99d8637af85f1ac65d7f04dfc83.
Its original graph BFS paths, recursive restrictions and exhaustive partitions
will be reused, not the production guard/certificate checker.

The receipt and production Tree canonical ordering are inputs under review.
For certificate vertex/edge ids only, obtain the parent's model metadata and
match its vertices by rooted descendant-label sets to the independently
parsed literal trees. Verify the entire rooted graph isomorphism, labels,
edge universe and orientation before translating any certificate. Thus no
production restriction, support, component or witness result is an oracle
for verification. Canonical numbering is shared metadata, explicitly named.

Independent checker: reconstruct S-C full original connected components;
require all components labeled, cost=distinct original edges, and r+1 parts
for nonempty input. Compare each submitted full-vertex set, label set,
source restriction and target support to independent values. For each local
witness require a complete partition of its component labels, equal rooted
restrictions, pairwise disjoint original supports within both trees, and
submitted target support equality. Check local cuts are distinct original
internal edges, disjoint from C; reconstruct the cut graph restricted to the
full component vertices and require exactly the submitted leaf partition,
no empty local pieces, and cost=local cuts=pieces-1. Recompute hull-intersection
degrees for pure geometry and compatible-or-three membership independently.
Require every local witness cost<=floor(b/2) and tau upper bound=max costs.

Controls before the18 covers: empty, singleton, identical pair, incompatible
rooted triple at b2 with cost1 local witness, and actual pure crossed-pair
hulls. Clean twins must pass; perturb local cost, target support and full
source vertices separately and require rejection. At budget0 the incompatible
triple cost1 witness must fail the half-budget check. Test the coverage
comparator with the known equal-halves pair: the nonempty valid guard from
precut clade{c,d} omits every optimum at b1, whereas pendant b preserves an
optimum. Both guard certificates themselves are valid; existential survival
must distinguish them.

Then load the nine frozen CB1 inputs and reconstruct all original optimal
partitions independently by enumerating label partitions (at most six labels).
Generate covers at b=opt,opt+2 with production partitions/oracle/packing/
exact_row helpers replaced by raising functions; score only after restoring
them. Verify every emitted certificate by the above checker, compare literal
generation outputs/stats with the pinned CB4 receipt, and count original
optimal partitions refining each prefix. Require at least one survivor per
cover. Independently score each component's actual original unmarked local
distance using compatible local partitions and original support checks;
require distance<=explicit cost<=floor(b/2). Record all18 covers and all
emitted certificates, including nonsurviving valid prefixes.

Measure the bounded18-cover run; no enlarged census or new construction run.
Review prefix dominance mathematically: at every state maintain a normalized
full original minimum transversal extending C; quotient and forced closure
may replace residual original edges, so do not insist on the SAME optimum.
Cost dominance may replace its prefix, but the replacement union must be a
full minimum transversal extending the current C. Early guards then preserve
that state's surviving minimum, even if witnesses differ. Seek an exact
counterexample if this invariant fails; finite success is not a universal
proof. Cache must include C because guard geometry depends on C.

Finally inspect the corrected RESULT diff and CB2 closure addendum against
the prior findings. No prior CB1 mathematical proof or old Lean release
review is recertified. Universal C1 and terminal-completion interfaces and
alpha generation bound remain open.
