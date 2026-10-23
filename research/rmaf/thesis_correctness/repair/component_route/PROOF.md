# Component proof of restricted normalization

This is a proposed proof for the precise reduced-forest statement in `PROOF-TARGET.md`. Fresh nonauthor verification is pending. The arbitrary-cutset compound statement remains false. The six named Lean theorems prove local binary-cut and two-exchange counting statements; they do not formalize the agreement-forest arguments below. Converting the second exchange to exact original-edge cutsets remains an explicit obligation. No global algorithm correctness or runtime result is claimed.

## 1. Definitions and sources

The source is the locally retained Whidden thesis text, printed pp.12–18, 101–103, and 112–116, with PDF page number equal to printed page plus 13. The reading ledger records the corresponding source strings. Page12 defines the unary labelled root rho, minimal connecting subtree, and suppression. Page15 defines a forest by cutting edges and taking the yielded forest. Pages16–18 define equal pendant subtrees, sibling pairs, component containment, and overlap. Lemma6.5 appears on pp.101–103. Its consumers are Lemma6.10 on pp.112–113 and the final exchange in Theorem6.12 on p.116.

All graphs below are finite rooted forests, directed away from their component roots. Their internal unlabelled vertices have two children; rho, when present, is a labelled component root with at most one child. Distinct labelled leaves are never identified. An endpoint subtree may contain several labelled leaves. A proper endpoint subtree has an incoming edge.

For a nonempty label block B within a component of G, write M_G(B) for the minimal connected subgraph containing its labels. Write G|B for the rooted tree obtained by suppressing unlabelled vertices with fewer than two children in M_G(B). Root positions in M_G(B) are inherited from G. In particular, a block containing rho retains rho.

A partition represents a forest of G when its blocks lie in components of G, the corresponding component trees equal G|B, and the subgraphs M_G(B) for distinct blocks are vertex-disjoint. Necessity follows directly from the disjoint components of G after the cuts: each minimal subgraph stays inside its cut component. For sufficiency, cut the incoming edge of the highest vertex of each M_G(B), when that edge exists. Descendant blocks detach at their own highest vertices. A block's minimal subgraph contains no other block's highest vertex, by disjointness. Every labelled vertex therefore lies in its designated block component; any component left over has no labels and disappears under suppression. Suppression of each labelled component gives G|B. This proves the partition criterion directly.

If H is obtained by cutting a yielded forest F of T, the same criterion proves that H is a forest of T. Each edge of F expands to a path of T whose internal vertices are unlabelled and were suppressed. Distinct F edges have disjoint path interiors. Components of F came from disjoint components after the earlier T cuts. Expanding the disjoint minimal subgraphs for H consequently preserves disjointness; inserting unary vertices preserves their rooted restrictions. Branches pruned during the earlier yield contain no labels retained in F. This proves semantic composition for forests. It does not assign a new exact original-edge cutset or prove a cut-count identity under suppression; those are separate obligations.

## 2. Endpoint fragments

Assume F1,F2 and a,c satisfy the frozen target: their entire endpoint subtrees A,C are equal in the two current forests before E is cut. In F1, a and c are siblings with parent p. Let P be their F2 path and u their F2 LCA. Let E2⊆E preserve A,C intact and make their roots siblings after yielding.

No E2 edge lies on P or strictly inside A or C: such a cut would separate endpoint labels or change an endpoint subtree. Every branch leaving an internal vertex of P has no label connected back to P after E2. Otherwise its retained branch would prevent a and c from being siblings. Since E contains E2, the same statement holds after E. Label-free remnants attached to P have no effect on the yielded forest.

Let S_a and S_c be the labels connected to the endpoint roots a,c after E, restricted to A,C respectively. These sets may be empty. If S_a is nonempty, the union of paths from a to S_a lies entirely in the cut component of a. It is therefore disjoint from the minimal embeddings of every other component inside A. Under the equal-subtree correspondence, the same disjointness holds in F1. The analogous statement holds for C. This includes the possibly unary stem above the LCA of S_a or S_c; omitting that stem would leave a gap in the overlap argument.

Every label outside A∪C that can join an endpoint after restoring path edges must reach P through the incoming edge of u. Call the set of such labels W. If u is a component root, W is empty. All other labelled components remain unchanged by restoring P and possibly cutting the incoming edge of u.

The proof uses the following restricted survival condition. If exactly one path edge is cut, W is nonempty, and the endpoint component separated from u has a label, then the u-component must also contain a label from A∪C. This is the `N_anchor` condition. Requiring both S_a and S_c to be nonempty is a sufficient simpler premise. No survivor is required when at least two path edges are removed, or in the degenerate one-cut cases described below.

## 3. Normalization

Put D=E∩edges(P). Restore every edge of D. If |D|≥2 and u has a parent, cut the incoming edge eu; otherwise add no edge. Call the resulting set E'. Edges strictly inside A,C and outside the displayed connecting region are unchanged.

For D empty, the forests are identical.

For |D|=1, the cut separates a from c. Exchange their names if necessary so that a lies on the side separated from u. The only possible changed labelled blocks are S_a and S_c∪W; normalization replaces them by S_a∪S_c∪W, omitting empty sets. If S_a is empty, the labelled forest does not change. If W is empty, the joined block lies entirely in A∪C. Its rooted restriction is the join of A|S_a and C|S_c, with any empty branch suppressed. Equality of the whole endpoint subtrees and their sibling relation in F1 establish this topology in both forests. The endpoint-fragment observation in §2 excludes overlap with all other pieces inside A,C. Minimal embeddings using only labels outside the pendant clade A∪C cannot enter that clade, so they cannot overlap the joined block.

The remaining one-cut case has S_a and W nonempty. The survival premise gives S_c nonempty. The old block B=S_c∪W was an agreement component. In its rooted topology, the restriction on S_c occupies one pendant subtree. In both forests, normalization replaces that subtree by the sibling join of A|S_a and C|S_c; the topology on the rest of B is unchanged. Hence the resulting rooted restriction agrees.

For the overlap check in F1, M_F1(B) already contains the stem from S_c through c and p toward W. Adding S_a extends that minimal subgraph only along the edge p–a and the root-connected fragment inside A. The fragment is disjoint from all other component embeddings inside A by §2. The vertex p already belongs to the old B embedding, so no other component embedding uses p. All remaining added vertices lie inside A. Thus the new component has no overlap.

For |D|≥2, cutting eu, when it exists, separates all outside labels W from the reconnected path. If eu is already cut, adding it again changes nothing. If eu does not exist, W was empty. The changed blocks are therefore S_a∪S_c and W, again omitting empty sets. The first lies inside the common pendant clade A∪C in F1 and has the sibling-join topology described above. Its embedding is disjoint from every detached endpoint fragment by §2 and from every outside block by the pendant-clade property. The block W is a restriction of one old agreement component, so its rooted topology remains compatible and its minimal embedding remains disjoint from all unchanged blocks. The two new blocks cannot overlap: W has no label inside the pendant clade A∪C. Empty S_a or S_c creates no extra case after suppressing empty branches.

The partition criterion now proves that F2~E' is an AF of F1,F2. Semantic composition from §1 gives an AF of T1,T2. Component containment is retained as an explicit active-state premise; this proof uses the stronger assumed active AF compatibility directly and does not silently replace one with the other.

The exact count on the current edge set is

|E'| = |E| − |D| + δ,

where δ is 1 precisely when |D|≥2, eu exists, and eu is not already in E\D. Otherwise δ=0. The edge eu is outside P. Thus |E'|≤|E|. In the absent-parent case δ=0; no fictitious edge is introduced.

The conditional surviving label in the one-cut attachment case is the smallest survival premise used in this derivation. It is a sufficient condition for this argument, not a necessity characterization of all tree pairs. Extra topology agreement can make a particular instance work even when that condition fails. The frozen counterexample shows why the condition cannot simply be deleted from a uniform arbitrary-E theorem.

## 4. Empty common subtrees

Let A be a proper pendant subtree, identical as a labelled rooted tree in current forests G1,G2, with root v. Let E yield an AF of G1,G2. Suppose no A-label remains connected to v in G2−E. Let I consist of the E edges strictly inside A, and let ev be the incoming G2 edge of v.

Every old agreement component containing an A-label lies wholly inside A: a path to an outside label would pass through v, contradicting emptiness of its root fragment. Undo all cuts I and cut ev. The new labelled component is exactly the entire subtree A. Every outside component and its labels remain unchanged. In G1, an outside component's minimal embedding cannot enter the proper pendant subtree A. The new A component therefore has no overlap with them, and it has the same rooted topology in G1 and G2. The partition criterion proves AF preservation. No optimum or completion assumption was needed for this construction.

If v is a leaf, the supposed empty root fragment is impossible. Otherwise v is binary. Each child branch contains a label, and disconnecting every such label from v requires at least one internal cut in each of the two disjoint child branches. Therefore |I|≥2. The exact replacement cost is

|(E\I)∪{ev}| = |E| − |I| + 1_{ev∉E} ≤ |E|−1.

A minimum-cardinality AF cutset therefore leaves a labelled root fragment in every proper common pendant subtree. This applies simultaneously to a,c and any common uncle x. Minimum means minimum among all AF cutsets on the specified current forest, not inclusion-minimal and not minimum among extensions forced to retain I. A forced-extension optimum can fail the conclusion because the repair removes members of I.

`EmptyRoot.lean` formalizes the binary cut lower bound and strict local cost inequality for every finite cut-decorated binary tree. Its model has a label at each leaf; the correspondence of an actual endpoint subtree to this model uses precisely the binary-validity hypothesis. AF preservation is the partition argument above and is not asserted as a Lean theorem.

## 5. Lemma 6.10

The source on pp.112–113 starts with common endpoint subtrees a,c and a common uncle x. It chooses an AF extension E0 whose cardinality is the global minimum for the current F2. Applying §4 separately to A,C,X shows that all three endpoint root fragments survive E0. The pendant cuts P={eb1,eb2} lie outside these three subtrees, so adding P does not erase any of those fragments.

Apply full path normalization from §3 to (a,c). The operation restores every cut on their path and changes no edge strictly inside A,C,X. The new root u is connected to both surviving endpoint fragments. The fragment at x remains unchanged. In the base forest G=F2~P, before applying the residual cuts, the whole subtree rooted at u consists of the two equal endpoint subtrees joined as siblings, so it equals the corresponding F1 subtree. Thus the second pair (x,u) has surviving fragments, including the compound endpoint u. It does not need a new optimality assertion for the intermediate E0'. The source's second invocation of Lemma6.5 is justified by fragment propagation once the cutset has been represented on this yielded forest.

Representing the second exchange on actual current edges requires a separate result: a proof must map the first normalized cutset to the actual edges of F2~P, preserve its yielded forest and both root fragments, and carry its exact cardinality or a sufficient upper bound. No preservation under suppression or contraction is assumed here. Semantic topology composition in §1 alone does not prove that cost statement.

The following count gives one inequality in place of the source's casewise equalities and permits restoring all actual path cuts, including any not in its displayed local E3. Let p=|E0∩P|. Let s≥1 be the number of E0 path(a,c) cuts (ea is among them). Let q be the number of E0 cuts among {ex,eu}. The selected local set E⊆E0 contains at least two edges in these disjoint groups, so p+s+q≥2. Let δ∈{0,1} be the first normalization's newly inserted incoming edge; δ=0 if s=1. The second path has r=q+δ cut edges, assuming the explicit edge representation just described. Let ε∈{0,1} count the second normalization's new incoming edge; ε=0 if r≤1. Missing parents make the corresponding insertion count zero.

The net change in cut count is

2 − p − s + δ − r + ε.

The net change is nonpositive. If ε=0 this follows from r=q+δ and p+s+q≥2. If ε=1 then r≥2; either δ=0 and q≥2, or δ=1 and s≥2 and q≥1. In both cases p+s+q≥3. The six-variable inequality and its implication for the final cut count are checked by Lean in `two_exchange_savings` and `two_exchange_cost_nonincrease`. The final cutset retains both pendant cuts. Once the exact edge representation is supplied, these facts give the local conclusion needed in Lemma6.10 without treating u as an ordinary leaf.

## 6. Theorem 6.12

In the final p.116 exchange, E0 is a global minimum AF cutset of the current F2, includes ec, and already includes one of eb1,eb2. Common-subtree lemma §4 gives surviving root fragments at a and c. Adding P={eb1,eb2} costs at most one new cut and changes neither fragment.

Apply full normalization of (a,c) after adding P. Let s≥1 count all path cuts, including ec. If s=1, normalization saves one cut. If s≥2, it saves at least s−1≥1, since at most one incoming edge is added. Consequently the final cutset has at most |E0| edges and includes P. This is enough for the earlier pendant branch to attain the same optimum. The argument does not require the source's displayed set E0\{ec}∪P to be the normalized set. Restoring additional path cuts can only improve this count, and §3 supplies the required AF preservation with the correct possible incoming-edge insertion.

The local argument assumes the source's genuine minimum E0 and active-state compatibility. It does not prove that every marked search state maintains those hypotheses, or reconstruct the entire leftmost-promising-path proof.

## 7. Executed evidence

The four original frozen controls and four corrupted-expectation catches ran before the first adversary. The narrowed controls additionally excluded the compound counterexample by its missing survivor, checked a concrete bad empty-subtree repair that omits the incoming cut, checked a positive compound normalization, and enumerated the counterexample's true minimum cut count (1). The bad repair failed AF as expected.

The complete n=4 family examined all 225 ordered rooted binary tree pairs, with F1 whole or rho-detached where compatible, and F2 whole or rho-detached. It examined 51,516 AF cutsets for eligible common-sibling pairs, 43,710 satisfying N_anchor, 41,052 satisfying both-survivor N, 9,984 raw compound-pair premises, 4,776 absent-parent premises with at least two path cuts, and 5,070 empty-subtree repairs. No narrowed normalization or repair failure was found. These are distinct denominators; raw compound counts are not presented as counts satisfying N.

The bounded n=5 run examined 20,000 AF cutsets while starting 24 ordered tree pairs: 15,429 N_anchor premises, 14,740 both-survivor premises, 2,761 raw compound-pair premises, 1,428 qualifying root boundaries, and 1,792 empty-subtree repairs. It found no narrowed failure. The n=5 run was not exhaustive. Both searches use ordinary endpoint subtrees that already exist in the current forests; they do not substitute for the edge translation in §5.

All six named Lean theorems compiled. Their only reported axioms were subsets of propext, Quot.sound, and Classical.choice. A deliberate claim that an empty binary root needs at least three internal cuts was rejected by Lean on the two-child leaf example. The exact receipts, logs, and source hashes accompany this document. Fresh verification of the prose proofs and consumer interface is still required.
