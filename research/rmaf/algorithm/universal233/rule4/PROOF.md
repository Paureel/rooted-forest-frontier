# Original Rule4 graph proof — author draft

Status: author kernel proof, awaiting fresh nonauthor acceptance.
Rule4Cover.actual_rule4_cover proves the uniform original graph statement;
Rule4Solve proves the conditional minimum and final original certificate.
All three full-algorithm milestones, a smaller global base and novelty remain
OPEN. FIRST-GAP.md states the remaining acceptance and whole-solver limits.

## Model and source

The retained `sources/baseline/split-or-decompose-v2.txt`, PDF pp3–4, defines
T[A] as the minimal original connected embedding and requires distinct agreement
blocks to have vertex-disjoint embeddings in both trees. Its footnote2 omits
rho. Pages6–7 define pendant outgoing original child arcs and Whidden t=1.
Rule4 and Lemma12 are on PDF pp17–18. The exchange case is in Lemma12 on PDF p18, where B meets X2 and excludes c.
SOURCE-LEDGER.md carries the exact retained passage. The argument below derives
the replacement topologies and global embedding separation from the original
source model.

T,S are original rooted binary trees, bijectively labelled by the same X. All
embeddings below include unsuppressed original path vertices. T has actual
cherry {a,b}. The original S path a–b has exactly two outgoing child edges,
with pendant label sets {c} and D0=X2, c adjacent to a; {a,c} is an actual
S cherry. There is no common cherry and no Whidden t=1 in either tree role.
Both orientations of either cherry and either original traversal order of the two pendant heads are admitted. The formal guard is a permutation of the actual two-element pendant list. No root leaf is added.
For a component bound k, the initial cut budget is q=k−1.

Let W be the original S subtree rooted at lcaS(a,b), and R=X\leaves(W).
Every descendant of that LCA is either on the a–b path or is in one of its
outgoing child subtrees: following its path down from the LCA, the first child
edge leaving the a–b path is one of the two named edges. Consequently

    leaves(W) = {a,b,c} ∪ D0.

This remains true when W=S, so R may be empty. The two pendant heads are
incomparable, and each has a nonempty leaf set. Deleting them gives precisely
Q1=({c},D0,R∪{a,b}); deleting the original a-leaf edge gives
Q2=({a},X\{a}). The notation denotes blocks, not an order imposed on outputs.
Both partitions are literal original residual components; no leafless region
is discarded. Q1 costs two distinct original cuts and Q2 costs one.

For branch3 set P=the original T path a–c, and list ALL original child edges
whose tails lie in P and heads do not. Their heads are an antichain. Deleting
these m edges gives their nonempty descendant label sets followed by the
remainder containing a,c. Thus Q3 has exactly m+1 nonempty original components.
The original b-leaf edge is one of these edges: its tail is a's T cherry
parent, which is on P because c differs from a,b. Hence m≥1. Since {a,c} is
an S cherry, m=1 is an actual Whidden t=1 in swapped roles and is excluded.
Therefore m≥2. Branch3 target is S, cut source is T, and its cost is m.

## Graph facts used, including original-path versions

A. If nonempty A⊂B is the intersection of B with a pendant original subtree
of U, then U|B displays A as a proper rooted cluster. If U|B=V|B, the same
cluster occurs in V|B. An edge above that cluster in the restricted tree is
represented by a nonempty downward path in V[B]. Choose any original edge on
that path. All selected A leaves lie below it and all selected B\A leaves
lie above/outside it. Thus V[A] and V[B\A] are disjoint in the ORIGINAL V,
including suppressed path vertices. Other labels below the chosen edge are
irrelevant. This explains why transferring only abstract restricted vertices
would be insufficient. The frozen SourceEdge.descendant_final_source_edge is
a retrieved formal instance of the original-edge cluster realization fact.

B. A component H crossing a pendant subtree boundary must use that boundary's
original parent. If another block's embedding uses the parent, H is impossible
by agreement disjointness. This is the unique path property of a tree: take one
H leaf below the edge and one outside; their path passes through its parent.

C. If {x,y} is a cherry in U and x,y are in one agreement block B, then B has
no selected leaf in any outgoing pendant group along the V path x–y. Otherwise
U|B retains cherry xy while V|B does not, contrary to rooted restriction
agreement. Every other block must stay on one side of each such edge by B.
Therefore the agreement refines the partition cutting all those V edges.
This applies for any number of outgoing edges, not only two.

D. Let actual cherry {a,b} be in T, let b be a singleton agreement block, and
let B contain a and at least one other leaf. Its original T embedding contains
a's parent p, because that other leaf lies outside p's two-leaf subtree. Adding
b to any K⊆B containing a adds at most p and b to T[K]. Both p and the a–p
edge already belong to T[B]; only the original b leaf may be new. No other
agreement block can occupy those vertices once singleton b is removed.

## Cover for every original agreement F

Take any original F. If singleton a is a block, F refines Q2. Otherwise apply
the completed original hard-parent theorem (Safety.actual_hard2_unordered_safety)
to T,S,a,b and the two actual S pendants. Either F refines Q1 or singleton b
is a block. This theorem is a development import with its complete hypothesis
list, not an assumption about the desired Rule4 cover. We therefore need only
consider singleton b, a nonsingleton a-block B, and F not refining Q1.

If c∈B, apply graph fact C to the S cherry ac and the original T path a–c.
It gives that F refines Q3. This constructs the role-swapped branch directly.

Suppose c∉B and B∩D0 is empty. B must meet R: b is singleton, c is absent,
and B is not singleton a. The path from a to any such R leaf traverses the
parent of each original S pendant head. Every other block is therefore unable
to cross either pendant boundary by fact B. The block B itself is in
R∪{a,b}. Hence every block is contained in one of {c},D0,R∪{a,b}, and F
refines Q1, contrary to the remaining case. If R is empty, the supposition
already makes B singleton a and is impossible.

The only remaining case is c∉B and D=B∩D0 nonempty. Define

    K = B\D0 = {a} ∪ (B∩R),    E = K ∪ {b},
    F' = (F\{B,{b}}) ∪ {D,E}.

These are actual label blocks. D is nonempty and K contains a, so both new
blocks are nonempty. Original labels occur exactly once. Removing two blocks
and adding two gives |F'|=|F|, even when K={a} or D is a singleton.

First c is singleton: S[B] contains a and some d∈D0, hence contains the
original ac cherry parent. A c-block connecting c to any second label would
use that same parent, violating disjointness. Every other nontrivial block H
is either wholly inside D0 or wholly inside R. Indeed, S[B] also traverses
the parent of the D0 pendant edge; a block containing a D0 leaf and an outside
leaf must traverse that parent and is impossible. After excluding a in B,
singletons b,c and D0, the only labels left are R. This is a GLOBAL statement
about all untouched blocks, derived from original source embeddings.

Topology of D is inherited by restricting the original agreed B in both
inputs. Since D0 is pendant in S, D is a proper cluster in S|B and therefore
in T|B. Fact A gives original disjointness of T[D] and T[K]. To compare E's
topologies, first restrict B to K, obtaining T|K=S|K. Both T|E and S|E are
obtained from this same tree by replacing leaf a with rooted cherry {a,b}.
For T this follows from its actual ab cherry. For S, after c and D0 are
removed from W, W restricts to cherry ab; all K\{a} labels lie in R.
Thus T|E=S|E, including the boundary K={a}. No whole-parent D0 agreement
or topology assumption is being used.

Target clearance: T[D] and T[K] are disjoint by fact A. Adding b to K adds
only vertices contained in T[B] together with the now removed singleton b
(fact D). D cannot contain p because all its labels are outside p's subtree
{a,b}. Thus T[D] and T[E] remain disjoint. Both new embeddings are subsets of
T[B]∪{b}; every untouched old component was disjoint from that set. This
also handles the degree-two vertices that suppression would hide.

Source clearance: S[D] lies inside the original D0 pendant subtree; S[E]
never enters it, because E contains no D0 label. Thus the new blocks are
source-disjoint. Untouched D0 blocks stay inside that subtree, and singleton c
uses only its leaf, so both are clear of E. An untouched R block never enters
W: W is a pendant clade and that block has no W labels. Outside W, every
vertex of S[E] already belonged to S[B], since adding b and deleting D only
changes connections inside W. Original disjointness from S[B] therefore gives
clearance from every R block outside W too. S[D]⊆S[B] is automatically clear
of all untouched blocks. This proves global original source disjointness,
including optional B∩R labels; R=∅ is covered without a root convention.

All untouched topologies and their mutual separation are unchanged. Hence F'
is an original agreement with |F'|=|F|. Singleton c, the new D, the new E,
other D0 blocks and other R blocks all lie in Q1 blocks. Therefore F' refines
Q1. This completes the NO-LARGER original cover, not strict refinement of F.

The pinned root fixture has T=(((a,b),(c,d)),e),
S=(((a,c),(d,e)),b), and F={{a,d},{b},{c},{e}}. F refines none of Q1,Q2,Q3,
while F'={{a,b},{c},{d},{e}} refines Q1 at the same size. The outside fixture
adds common singleton f above the displayed trees and takes B={a,d,f}; the
new block is E={a,b,f}. These finite examples are executed, not universal proof.

## Child solver induction hypothesis and minimum reconstruction

For each printed branch i, let Ui be its literal target, Vi its literal original
cut source, Qi the literal source partition, and di its actual cut count. Its
materialized source forest is the list (Vi|C : C∈Qi) in literal component order.
The child-specific exact IH at budget r is:

* return None iff no agreement of Ui with that whole literal source forest
  is attainable with ≤r additional cuts;
* otherwise return a minimum component-count such labelled forest partition G.

The completed OutputState.agrees_iff_original and checked_materialization apply
because Qi is an original checked source cut partition with disjoint source
embeddings. They identify child agreements exactly with original agreements
on Ui,Vi refining Qi, with additional cost |G|−|Qi|. Qi need NOT be a valid
target embedding partition. The child IH is the only recursive solver premise;
no cover/exchange, original realization, minimum, or runtime fact is a record
field supplied by the caller.

Call child i only if di≤q, with r=q−di. All di≥1, so r<q. Given any original
F with |F|−1≤q, the graph cover constructs F'≤F refining one Qi. Nonempty
refinement gives |Qi|≤|F'|. Since |Qi|=di+1, di≤q and that child is called.
Its additional cost is |F'|−(di+1)≤q−di. The IH supplies a returned G with
|G|≤|F'|≤|F|. Every returned child G is an original agreement after swapping
back when i=3, and has

    |G|−1 = di + (|G|−|Qi|) ≤ q.

Thus choosing the minimum of the returned original label partitions gives a
global original minimum under q. If all children return None, no such original
F exists. Swapping exchanges (Ui,Vi)=(S,T) and the source forest T|Qi, not merely
a flag. RMAF.agreement is symmetric in its two original input trees, so output
labels need no relabelling. Exact singleton/deletion history is not erased.

Recover cuts ONCE on the original S from the selected labelled partition. The
completed FinalCutRecovery.recover_original_agreement provides an executable
original certificate with exactly |G|−1 distinct valid nonroot cuts and every
original residual component, up to component/label order. The Python path uses
a deterministic multi-source extension of the same disjoint minimal hulls and
checks its full original residual graph. Neither path unions child cut sets.
The exact additional-cost identity pays every child source cut.

## Normalized callback mass and source work

At rational c≥2, literal costs are 2,1,m with m≥2. Since c>0 and c⁻¹≤1,
(c⁻¹)^m≤(c⁻¹)^2. Therefore total callback mass is

    c⁻²+c⁻¹+c⁻m ≤ c⁻¹+2c⁻² ≤ 1.

Budget pruning removes nonnegative terms. At c=233/100 the worst-case mass is
43300/54289; the full-root fixture attains that local upper bound. This does
not by itself establish the whole faster algorithm's global recurrence.
Selection, scans and restrictions have a qualified polynomial local toll.
The actual formal final recovery is called once after minimum selection and
is charged separately by finalPolynomial(S,G)·c^q in
Rule4Solve.solveCuts_recovery_work. COST-MODEL.md states the source-operation
qualification and distinguishes the Python development reconstruction. No recursive callback is free, and no original-source data work
is paid using CPU activity, helper invocation alone, or an uncharged root leaf.
