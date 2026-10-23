# Transition ledger (source reading plus independently executed arithmetic)

Notation: K is the remaining cut budget (the thesis writes k); s is the number of pendant nodes (the thesis also uses q for this). p=|P| and r=|Q| are analysis credit counts. W(p,r)=(2+r)/2^(p+1). A child (d,p,r) has budget K-d. Every inequality below means **conditional on the source's structural prerequisites**; the arithmetic receipt is not a proof of those prerequisites.

## Algorithm transitions, printed pp104–111

| Case | Prerequisites after trivial reductions and all earlier cases fail | Candidate cut sets; budget decrease | Protection changes |
|---|---|---|---|
| AC (SC in Fig6.5) | endpoints in different F2 components | {ea}:1; {ec}:1 | none |
| B | same component, s=1 | sole pendant edge:1 | none |
| RB | an endpoint's F2 sibling is exactly the F1 uncle subtree | opposite endpoint edge:1 | none |
| RB* | shallow c is child of LCA; pendant subtrees exist in F1 and make the specified chain uncle | ea:1 | none |
| 2B | s=2 and F1 uncle is F2 sibling of LCA | both pendant edges:2 | none |
| BCY | protected uncle exists in F2 as child of b1, s≥2 | all pendant edges:s; {ec,ey}:2 | none |
| A2BC, ec unprotected | s=2 | ea:1; both pendants:2; ec:1 | C-child protects ea in F1 and ea plus both pendants in F2 |
| A2BC, ec protected | s=2 | both pendants:2; ea:1 | A-child protects both pendants in F2 |
| A3BC | s≥3 | ea:1; all pendants:s; ec:1 | C-child protects ea in F1/F2 |

Every candidate branch is suppressed if its cut set meets a protected edge or contains a component-root incident edge whose sibling is protected (printed p107). Suppression transports protection by logical OR over the two surviving edges. New protection does not consume budget. Within an invocation every successful trivial step reduces |Rt|, so it terminates after at most the initial |Rt| steps. A recursive edge consumes at least one unit, so a search path starting at q0≥0 has at most q0+1 recursive edges before the negative-budget failure test. Large pendant cuts can overshoot below -3; the thesis's footnote p117 compares only truncated worst-case decrements up to 3. A formal recurrence must distinguish actual negative budgets from those dominating representatives.

## Credit transitions, printed pp117–126

The full numerical list, including parameter choices, is in `../results/thesis-complexity-arithmetic.json` (44 diagnostic rows).

| Source group | Incoming credit | Children (cut decrement, p, r) | Structural prerequisite / unresolved point |
|---|---|---|---|
| G1 simple | 0,0 | at most two (1,0,0) | earlier cases or pruned branches |
| G1 A2 | 0,0 | (1,0,0),(2,0,0),(1,1,0) | ordered first branching case A2 |
| G1 A3 | 0,0 | (1,0,0),(3,0,0),(1,1,1) | s≥3; use s=3 for domination |
| G2 one | 1,r | (1,0,0) | one legal branch; clears credit |
| G2 BCY | 1,r | two (2,0,0) | both cuts cost≥2 |
| G2 two | 1,r | two (1,1,r) | both children move to G3 |
| G2 A2 | 1,r | (1,1,r),(2,1,r),(1,2,r) | third child adds protected u |
| G2 A3 | 1,r | (1,1,r),(3,1,r),(1,2,r+1) | source p119 prose says Q union {v}, formula says {u}; subset invariant requires u |
| G3 one | 1,r | (1,0,0) | cannot merge credited a,d; only one legal branch |
| G3 after G1 A3 | 1,1 | (1,0,0),(2,0,0) | resets both credits |
| G3 after G1 A2, current A2 | 1,0 | (1,1,0),(2,0,0) | C cuts d, B resets |
| G3 after G1 A2, current A3 | 1,0 | (1,1,1),(3,0,0) | C cuts d and changes Q |
| G3 double | 2,r | at most (2,0,0) | both endpoints protected; source proves ≥2 pendants |
| G4 one/BCY/two | 1,r | same three patterns as G2 | connectedness a~e and group progression needed |
| G4.1 A2 | 1,r | (1,1,r),(2,1,r),(1,2,r) | union lift of G1 |
| G4.1 A3 exception | 1,r | (1,1,r),(3,0,0),(1,2,r+1) | **arithmetic fails for r=0,s=3; reachable witness supplied** |
| G4 2B exception | 1,r | (2,0,0) | reset both credits; arithmetic passes |
| G4.2/G4.3 union | outer plus local P,Q | lift G2/G3 by set union except resets | the A3 lift creates |P|=3 on the retained 13-leaf trace; source promises ≤2. Other count-only variants remain abstract diagnostics. |
| G5 one | 1,r | (1,0,0) | source excludes merge, then at most one child |
| G5 two | 1,1 | (1,0,0),(2,0,0) | Q nonempty |
| G5 r=0 two | 1,0 | **excluded** | arithmetic would fail; source's pp125–126 geometric exclusion must be proved, never silently allowed |
| G5 double | 2,r | zero children or (2,0,0) | both endpoints protected; no merges; two-pendant lower bound |
| G6 | 0,0 | external induction | source says no outstanding P escapes the local block |

All actually enumerated standard transition masses pass except the identified G4 exception and the deliberately listed **source-forbidden** G5 r=0 transition. The latter is not a defect finding. The |P|=3 union rows were initially abstract diagnostics. The A3 variant with incoming r=1 is now reached by the retained 13-leaf trace (pendant count four); the other variants remain unproved reachable.

## Runtime overhead and output

The source claims O(n) local work by adapting Chapter3 arguments (p116); this arm has not formalized that adaptation. A direct implementation can use O(n) tree copies and rebuild paths/depths in O(n) per trivial reduction, giving a transparent O(n³) local upper bound and O(q0) branching-stack depth. Thus even a repaired exponential proof would currently yield a conditional O(2^q0 n³) bound from this arm; claiming the sharper O(2^q0 n) also requires the data-structure argument. Recording chosen cuts and replaying them to produce the agreement forest costs polynomial additional work. The initial unary rho root is retained. At the optimum in this convention qopt=m_rho-1, so 2^qopt=2^(m_rho-1). A decision budget q0 merely allows at most q0+1 components. No unaugmented-root conversion is asserted here.
