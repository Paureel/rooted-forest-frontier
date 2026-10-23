# A source-history counterexample to the outside-sibling premise

A legal history from an unprotected input reaches the exceptional G4.1 state with its retained endpoint inside a's protected sibling. This refutes applying the geometric candidate's outside-sibling hypothesis to every source history. The candidate explicitly assumes that hypothesis, so its conditional local conclusion is not refuted. The resulting C subtree has two calls and satisfies the proposed bound in this witness.

The coordinator first found a locally protected example and then constructed the initial unprotected trees below. Its first replay reused the geometric author's checker. The nonauthor reviewer subsequently replayed the complete history with its independently written checker and passed 60 physical/credit checks. A concrete Lean file checks 11 finite facts. The reviewer recompiled them, added two label/top checks, and rejected a false-outside certificate. Its completed addendum is `fresh_review/new_history/ADDENDUM.md`. Original review and proof files are preserved.

Use a labelled unary rho root above each displayed binary tree. All twelve ordinary labels are distinct, all edges start unprotected, P=Q=empty and the initial budget is 20.

```
T1 = ((((((a,t),d0),c),d),((x,y),h)),((W,X),(Y,B)))
T2 = (((a,((W,(x,X)),(d,(y,Y)))),(t,(c,(d0,B)))),h)
```

The following sequence belongs to the full permitted recursive-call tree. It does not assert that a success-short-circuit execution visits these branches.

| Step | Ordered pair | First applicable rule | Chosen child | Legal children | Credits after this child |
| --- | --- | --- | --- | --- | --- |
| 1 | (a,t) | A2BC | C, cut t | A,B,C | P={a}, Q=empty |
| 2 | (d0,a) | A3BC | A, cut d0 | A only | P=Q=empty |
| 3 | (a,c) | A2BC | C, cut c | C only | P={a}, Q=empty |
| 4 | (d,a) | A2BC | A, cut d | B,A | P={a}, Q=empty |
| 5 | (x,y) | A3BC, three pendants | State J | A,B,C | Input P={a}, Q=empty |

At step 2 the source's G3 sole-child rule resets the analysis credits. Physical protection of a persists. Step 3 therefore begins a new empty-credit G1 invocation with an already protected a. Printed p118 assigns P={a} to its A2BC C child without requiring all three nominal children to be legal. Step 4 is the two-child G3 A2BC endpoint continuation, which retains P={a} and Q empty. This trace does not use the disputed p119 Q-union assignment.

At the new G1 call, a and x have equal F1 depth 5; their F2 depths are 4 and 7. The deepest protected F1 attachment belongs to a, so the eligible region is the cherry (a,c). Pair (x,y) is ineligible. Thus choosing (a,c) is legal even though x is deeper in F2.

At J, define U=(W,(x,X)) and V=(y,Y). The active F1 fringe is `(a,((x,y),h))`. The F2 sibling of a is b=(U,V), and both U and V incoming edges are protected by step 4. The retained endpoint x lies inside b. The x–y path has the three unprotected pendant edges X,W,Y; x is deeper than y, all earlier rules fail, and all three A3BC branches are legal. The remaining budget is 16.

The C child cuts y and protects x. Its next selected pair is (x,h), whose only legal continuation cuts h. The resulting pair (x,a) has no legal child. The C subtree therefore contains two invocations. The witness changes the required structural case distinction; it supplies no asymptotic lower bound and no failure of the joint runtime inequality.

The next unresolved case is a C-prefix bound for reachable states with selected endpoints inside the inherited protected sibling, including the protected subtrees left by the preceding G3 A2BC cut. The source-history counterexample prevents replacing that case by the outside-sibling argument. The credited A continuation and the proposed frontier annotation remain separate obligations.

Reproduction files are `history-reachable-probe.py`, `HistoryTrace.lean`, and `FalseHistoryTrace.lean`. The probe's explicit tree/branch data and the positive/negative Lean logs are in `../../results/thesis-runtime-repair-history-*.json/log`. The generic Lean tree functions are reused from the original `Trace.lean`; the source phase/credit interpretation is stated explicitly instead of being hidden in an abstract transition table.
