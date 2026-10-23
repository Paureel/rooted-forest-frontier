# Frozen component-route targets — 2026-10-14, before proof construction

## Failed-form tombstone

Arbitrary-E normalization for equal compound sibling subtrees, even with finite binary validity, source-forest validity, component containment, and actual active AF compatibility, is FALSE. Exact witness: AD​VERSARY.md and the frozen pilot receipt. Adding existence of the LCA parent does not fix it. No later restricted proof changes this verdict. This is a structural active-state witness, not an algorithm reachability claim.

## Notation and sufficient theorem N

T1,T2 are finite rooted binary trees with a labelled unary rho root. F1,F2 are yielded forests of T1,T2 on the same full label set. Every label block of F2 lies within a block of F1. Nodes a,c are distinct sibling roots in F1 and have equal, label-preserving descendant subtrees A,C in F2 *before the additional cuts*. They are connected in F2. E is a subset of actual current F2 edges, and H=F2~E is an AF of F1,F2 (and of the originals). E2⊆E has the property that F2~E2 retains the whole endpoint subtrees A,C and makes their roots siblings. Let P be the unique path a–c; u its LCA; D=E∩edges(P); and S_v the labels below endpoint v still connected to v in F2−E.

For the first, simple target require S_a≠empty and S_c≠empty. Compound endpoints remain allowed and cuts strictly inside their subtrees remain allowed. Define E'=E\D, with eu added iff |D|≥2 and u has a parent in F2. Claim: F2~E' is an AF of F1,F2 and T1,T2; |E'|≤|E|, with exact set cardinality |E'|=|E|−|D|+1_{|D|≥2, eu exists, eu∉E\D}. The missing-parent case adds no edge.

## Sharper survival target N_anchor

Use the same hypotheses, but replace both nonempty endpoint fragments by this one conditional requirement: when |D|=1, and the component of F2−E containing u has an outside label (outside A∪C), and the endpoint component separated from u by D has an endpoint label, the u-component also has an endpoint label. No survival premise is imposed when |D|≠1. This targets exactly the nontrivial attachment case; absence of either outside labels or detached endpoint labels is a separate degenerate case, not an implicit survivor.

N_anchor is a candidate sufficient theorem, not a claimed necessary condition for every tree pair. It is to be falsified independently before its proof is accepted. N is its simpler corollary.

## Empty common subtree lemma O

G1,G2 are finite yielded binary forests with an identical proper pendant rooted subtree A rooted at v. E is an AF cutset for G1,G2. Suppose no label of A is connected to v in G2−E. Let I be all E edges strictly inside A, and let ev be its incoming edge in G2. Claim: replacing E by (E\I)∪{ev} produces an AF, with |I|≥2 and strictly fewer cuts. No minimality premise is used in constructing the repair. Therefore a minimum-cardinality AF cutset cannot empty the root fragment of such a common proper pendant subtree. For a labelled leaf the fragment is automatically nonempty.

This lemma concerns subtrees identical in the current uncut G1,G2; it does not silently cover a node that becomes common only after additional cuts. All minimality arguments must name the actual optimization problem and actual current edges.

## Proof gate and boundary

First execute the narrowed adversary and empty-subtree repair on exact finite instances using the already independent evaluator, preserving the earlier freeze. Then give a component/partition derivation with minimal-embedding and topology arguments exposed. Try a meaningful Lean local combinatorial lemma with standard axioms only; finite checks are not a formal universal forest proof. Do not read sibling edge-route or parent compound scripts. Do not spawn.

The consumer audit must include Lemma6.10's first (a,c) exchange and second (x,u) exchange, and Theorem6.12's final exchange. Intermediate E0' in6.10 is not assumed optimal. Any suppression-to-original-edge or global marked-state obligation remains explicit and open unless supplied externally with its precise hypotheses.
