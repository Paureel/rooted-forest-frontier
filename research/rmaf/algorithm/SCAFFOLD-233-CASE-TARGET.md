# Remaining scaffold target for the 2.33 alternative

Conditional target, not a completed proof. Source: retained baseline v2
Lemma16 PDF pp25–26 and disjoint recursion pp9–10, read this session.
Keep source safety, graph, cut-realization and formal/executable interfaces
explicit; this case accounting cannot replace them.

The source's two most expensive structural families are common triple-edge
overlap and overlap chain. The next multi-color core target would replace
them by residual mass≤3/c² and≤4/c² respectively. The remaining classes
should use their actual decomposition query budgets rather than uniformly
reusing the weaker residual (1,2,2) wrapper.

1. Disjoint three-parent child: the earlier rule5 exclusion gives at least
   two non-homeomorphic parents. At pretest depth1, a single unresolved
   query loses at least one budget unit to another bad parent. For p≥2
   unresolved queries the source supplies p calls each losing2(p−1).
   Desired uniformly charged bound at c≥2 is one T(q−1), since
   p*c^(−2(p−1))≤1/c. The p=1 case must remain explicit.
2. One overlapping pair and isolated non-homeomorphic C (Lemma16 case3):
   one split ownership branch has core mass≤1/c. In the other, two bad
   disjoint parents survive. The desired combined bound is
   residual≤1/c+1/c², including its one paid split and the preceding
   disjoint loss. This yields full [1,1,3,4], already passing2.31.
3. Isolated homeomorphic C and single-edge overlap (last Lemma16 cases):
   if one parent is homeomorphic, rule6's exact prerequisites must be
   supplied; if both survive bad pieces, use the same disjoint budget
   accounting. When all four split pieces are homeomorphic, the source
   claims a one-cut optimum detected at depth1, so retain that exact
   polynomial case rather than spawning unpaid residual calls.
4. All live parents homeomorphic: rule7 applies to their isolated connected
   overlap group; its exact Fitch realization/reconstruction is a required
   import. Earlier reduced deletion witnesses in this class cannot refute
   a macro called only after rule7.

Every “desired” bound above is an obligation, not a granted structural fact.
The full algorithm must also check that the source case list covers its
actual vertex/edge intersection patterns, prove every import in Lean, and
charge generation and all polynomial work. In particular, a generic
triangle of three pairwise-overlapping subtrees need not have a common
edge; source hard-child reachability/exclusion conditions must resolve that
pattern rather than assume an arbitrary overlap graph falls in case1.

The simpler source fallback retains its true recurrence if these sharper
budgets are unavailable. A compiled arithmetic target does not authorize
charging the fallback as the new rule. An exact finite enumeration escape
keeps a candidate total, with its stated n^O(q) cost, until a proved FPT
production path exists for every state.
