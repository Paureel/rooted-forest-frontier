# Address-prefix characterization (independent route)

This is a derivation from the unchanged equations in `RMAF.lean:116–133`,
not a claim of a kernel-checked general extraction theorem.

Fix a tree t and a label list S. Let E(t,S) be the set of addresses of leaf
*occurrences* whose labels occur in S. Thus E(leaf x,S) is {epsilon} if
x is selected and empty otherwise. For node(l,r), E is the disjoint union
0E(l,S) union 1E(r,S), where bE prepends b to every address in E.
Occurrence sets are finite; repeated labels change no reasoning here.

Write q <= p when q is a list prefix of p. Define
R(E) = {q : there exists p in E with q <= p}.
For nonempty E, let c(E) be its longest common prefix and define
H(E) = {q : there exists p in E with c(E) <= q <= p}; H(empty) = empty.
The longest common prefix is defined by the usual finite-list operation:
starting at the root, continue while every address has the same next bit.
At a nonempty leaf occurrence set the sole address is epsilon.

1. Rooted-span lemma. The vertex set of rootedSpan S t equals R(E(t,S)).
Proof by structural induction on t. For a leaf the defining conditional gives
both alternatives directly. At a node with no selected occurrence in either
child, R(E) is empty and the induction hypotheses make both rooted spans
empty. Otherwise every occurrence has either initial bit 0 or 1; its
prefixes are epsilon followed by that initial bit prepended to all prefixes
of its remaining suffix. This is exactly the root cons and the two mapped
child lists at lines 121–122. In particular rootedSpan is empty if and only
if E is empty. The claim concerns membership; multiplicity is irrelevant.

2. Minimal-span lemma. The vertex set of minimalVertices S t equals H(E(t,S)).
Proof by structural induction on t, using lemma 1 for branch conditions.
For a leaf the empty/singleton alternatives agree. At a node:
(a) E_l empty: if E_r empty, the induction hypothesis on r gives empty
support and mapping preserves emptiness. If E_r nonempty, c(E)=1c(E_r),
and the intervals from c(E) to every selected occurrence are precisely
1H(E_r); this is line 131.
(b) E_l nonempty and E_r empty: c(E)=0c(E_l), so H(E)=0H(E_l), line 132.
(c) Both nonempty: E contains addresses beginning with each different bit,
so c(E)=epsilon. Every prefix of a selected occurrence belongs to H(E),
and conversely. Thus H(E) is {epsilon} union 0R(E_l) union 1R(E_r),
which is line 133 by lemma 1. The cases are exhaustive, including when
several occurrences have the same selected label.

3. Nonemptiness. An actual leaf occurrence with selected label makes E
nonempty. Its own address belongs to H(E), so lemma 2 gives nonempty
minimalVertices. A label selected but absent from t gives no such witness.

4. Connectivity for the exact Adj/Walk interface. Assume E nonempty and set
c=c(E). Every q in H(E) has c<=q<=p for some selected occurrence p. Starting
at c, append successive bits of the suffix taking c to q. Each intermediate
address z has c<=z<=q<=p and hence lies in H(E); each step satisfies
BridgeReview.Adj because the child is exactly parent ++ [bit]. Walk.refl
followed by Walk.step constructs a walk from c to q. Reverse the c-to-u
walk (Adj is symmetric) and concatenate with the c-to-v walk. This gives a
Walk in H(E) between arbitrary members u,v. Lemma 2 transfers this walk to
the exact minimalVertices membership predicate, without adding or dropping
vertices. This includes all unary vertices below c and none strictly above c.

5. Packaging and consumer. A nonempty output list is a :: rest; use a as
ConnectedSupport.first, rest as ConnectedSupport.rest and step 4 for its
connected field. Membership is definitionally the unchanged executable
output membership. GraphRegion's toRootedRegion retains that predicate.
For two such supports with overlapping member z and the second root depth
at most the first, GraphRegion's existing deepest_graph_root_in_neighbor
applies with its stated depth and overlap hypotheses. No label-uniqueness,
leastness, restriction-transport, algorithmic runtime, or novelty assertion
is part of this argument.

Formalization boundary: the independent Lean file proves step 4 for a
prefix hull and constructs its ConnectedSupport packaging, while separate
closed examples check the actual executable controls. The general equalities
in steps 1–2 and transfer to executable extraction in step 5 are derived here
but are not represented by a Lean theorem in this arm unless the receipt
explicitly records a later completed formalization.
