# Preconstruction controls v1 — 2026-10-15

Pinned before new construction or search. These are author development, with
completed rule5_local fixtures/evaluator already contacted; no independent
certification is claimed. Exact a,b,c,w,t,x,p,q labels below are strings.

Clean printed path fixtures to execute through literal original-cut materializer:

1. I: T=(t,((a,b),(p,(x,(q,(w,c))))));
   U=(((a,(w,(t,(x,(p,q))))),c),b). Expected actual admission, Case322,
   costs [2,1,2,2]; two distinct selected c-side arcs.
2. II: T=((((x,(a,b)),y),c),z); U=(((a,(x,(y,z))),c),b).
   Expected actual admission, Case322, costs [2,1,3]. The a+x+y
   original-cut union is three, and a claimed payment of two MUST fail.
3. III: T=(p,(x,(q,((a,b),(w,c)))));
   U=(((a,(w,(x,(p,q)))),c),b). Expected actual admission, Case322,
   costs [2,1,2]; entering-LCA arc is present and nonredundant.
4. Mirror every internal sibling pair of each clean fixture. Admission,
   class, costs and raw no-larger cover truth must persist after recomputing
   all literal addresses. Also swap input roles and adapt all role fields.

Guard-failing wrong-saving plant: on I let
F={{a},{b,c,w},{t},{x},{p},{q}}. It is a valid original AF with a singleton
and b nonsingleton. Splitting X then {c} adds exactly two components. The
claim 'a singleton implies split saving <=1' MUST fail. The missing guard is
that b's block does not simultaneously contain c and an X label. The actual
3(i) cover must retain an unused selected c-side arc instead.

Guard-failing malformed geometry: move c into the core subtree containing
a,b (the literal cluster no longer has disjoint c versus core). Such a pair
must not pass the Case322 actual-geometry checker. A cover theorem supplied
only with claimed boolean saving is inadmissible.

A comparator-twin run must reject exactly one deliberately corrupted expected
cost. Fresh source-audit Std-only controls are separately pinned before audit;
missing/duplicate producer occurrence, path and adapted-source-byte mutations
must each be caught. All failures and nulls are retained.

Time gate: first execute three fixed fixtures only. Measure a six-label
partition pilot before bounded AF enumeration. No old colored census and no
toolkit-wide suite. Universal conclusions require Lean theorems; finite
minima or coverage do not replace those theorems.
