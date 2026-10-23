# Independent review freeze — 2026-10-14

Status: source reconstruction frozen before reading the existing complexity report, transition ledger, JSON results, Python runtime, or Lean modules. The assignment disclosed the alleged nine-leaf and thirteen-leaf outcomes; this is therefore an independent semantic reconstruction, not a blind discovery of the candidate numbers. No thesis-correctness or transfer work has been opened.

Source actually read: `../sources/baseline/whidden-thesis-2013.txt`, Chapter 6 printed pp.103–107,109–126. Image inspection additionally covered printed pp.110,117,118,123 (PDF pp.123,130,131,136). Source-derived facts below are transcriptions/paraphrases, not new results.

## Frozen semantics

* pp.104–105: active roots Rt partition the remaining leaves. Only sibling pairs in Rt are processed. Common sibling pairs contract; a component root is removed from the active F1 tree. Success is |Rt|≤2 and is checked after the negative-budget failure test (Figure6.5 p.111).
* pp.107,110: an attempted F2 cut is omitted if it cuts a protected edge or a root-adjacent edge with protected sibling edge. Suppression inherits protection by logical OR of the surviving two edges. F1 protection is introduced on a in the C-child of A2BC/A3BC.
* p.110 image: protected F1 edges are pendant to a single root–leaf path; their bottom endpoints are in Rt. Eligible sibling pairs lie below the deepest top endpoint of a protected edge. Among those choose maximum F1 depth. Ties prefer separate components or the greater maximum F2 depth; residual ties arbitrary (pp.110–111). The text's pair orientation is checked wherever its deeper-first use matters.
* p.111 Figure6.5: case priority is AC (printed SC), B, RB, RB*, 2B, BCY, A2BC, A3BC. Earlier cases must be excluded before claiming A2BC/A3BC.
* pp.107,109: A2BC unprotected c children cut a, cut both pendants, cut c while protecting a in F1 and a plus both pendants in F2. If c protected, children are pendant cuts then a-cut with pendant protection. A3BC cuts a, all m≥3 pendants, then c with a protected in both forests.
* pp.109–110: RB is forced single cut if an F2 sibling equals the F1 uncle. RB* is the corresponding rooted pendant-chain condition. 2B requires exactly two pendants and the F1 uncle to be the F2 LCA's sibling. BCY requires a protected F1 uncle appearing as a child of the first pendant; cuts all pendants or c plus the uncle's sibling.

## Frozen proof model

Printed p.117 explicitly says “P is a set of up to two nodes” and “Q is a subset of P”. Parent edges of P are protected in F1. The target is B(k,p,q)=α·2^k·(2^-p+q·2^(-p-1))+p−3. I counts the invocation itself, as all recurrences start with 1. Top level p=q=0; p117 only inducts on smaller k with empty P. Other states are discharged through groups G1–G6, in reverse dependence order (p118 image).

G1 (p118): A2BC children (δ,p,q)=(1,0,0),(2,0,0),(1,1,0); A3BC=(1,0,0),(m,0,0),(1,1,1).

G2 (pp118–119): a carried singleton credit survives AC and two-call A2BC/A3BC, and survives the A/B children of three-call A2BC/A3BC. Their C-child adds u to P; A3BC also adds u to Q (one prose line says v while its displayed formula says u). A one-child case clears; BCY two-child case clears with both drops≥2.

G3 (pp120–121): a single credit with Q nonempty clears on its two children. With Q empty, A2BC/A3BC retain a only on the endpoint-cut child; A3BC gives that retained a a Q credit; the pendant child clears. Two protected endpoints allow at most the pendant child, with ≥2 cuts. These are conditional structural claims to check, not assumptions licensed globally.

G4 (pp122–123): inside the at-most-four-leaf F1 uncle subtree, repeat G1–G3 but union every output P,Q with the incoming G4 singleton P',Q'. Exceptions: G4.1 A3BC children are (P',Q'), (∅,∅), (P'∪{a'},Q'∪{a'}); any 2B clears both. Thus for incoming |P'|=1,|Q'|=0 and m=3 the normalized child sum is 1/4+1/8+3/16=9/16, against parent 1/2. This arithmetic alone does not establish the configuration reachable or invalidate the asymptotic theorem.

G5 (pp123–126) explicitly discusses only singleton or double P, followed by a G6 empty-credit reset. G4 union can syntactically create three credits (carried a plus local a',u') unless a structural exclusion prevents it; reachability must be checked.

## Frozen checks and failure conditions

1. Represent trees as explicit vertex/parent/children maps with edges carrying Boolean protection; rebuild adjacency after each operation. Do not import author runtime or its helpers. Compare exact canonical clusters only for node identity.
2. Before witness replay, planted common-cherry contraction and root/sibling protection examples must pass; a corrupted expected cut forest and an illicit protected cut must be rejected. Positive twins use the same checker path.
3. Trace checker must reject a valid but non-maximal-depth chosen cherry; positive twin chooses the eligible maximum. Corrupt an expected child budget by one and require rejection. No tuning after candidate replay.
4. Rational arithmetic uses Python Fraction with independently hand-declared source transitions. Test B(0,0,0) and a zero-child recurrence, a true ordinary A3BC transition, and a false exceptional-reset comparison with its true ≤9/16 twin.
5. Lean replay uses clean isolated dependencies and actual #print axioms output. Kernel rejection of an intentionally false proposition and acceptance of its true twin are required; compiler exit alone is insufficient. Distinguish finite data, arithmetic, and conditional complexity bounds.
6. A source-proof gap needs (i) source reading, (ii) exact local failure, (iii) reachable source-semantic state. A runtime lower bound needs an unbounded family and cannot follow from these finite checks. Short-circuit success can prune a full recursion tree; record which execution model each trace claims.

Toolkit consultation: BootLoops tools README has exact numerical/integrity tools but no rooted-tree branch/protection checker; reusing the existing problem runtime would break independence. A one-shot local review checker is justified. Pilot one tiny fixture before the bounded witness pair; no large census is authorized as a substitute for a proof.

## Outstanding

Candidate trace replay; precise repair obligation; isolated Lean replay; report and dashboard receipt.
