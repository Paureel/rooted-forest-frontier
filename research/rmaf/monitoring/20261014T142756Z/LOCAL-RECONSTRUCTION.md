# Independent local reconstruction

This is the fresh reviewer's reconstruction after the initial exact controls. The local forest arguments below are prose proofs. The Lean files checked in the review formalize only the separately named counting, list, walk, and conditional-logic statements. The general transport of optimal completions and protected original edges between arbitrary search states remains open.

## Restricted normalization

Use finite reduced rooted binary forests, with the unary labelled rho convention. F1,F2 are forests of T1,T2 on the same labels; each F2 component label set lies in one F1 component. A and C are identical proper pendant rooted labelled subtrees in the two current forests, with their roots a,c siblings in F1 and connected in F2. The actual-current-edge cutset E yields an AF of F1,F2. Some E2⊆E leaves the whole A,C intact and makes their roots siblings after yielding. Let P be the original a–c path, u its LCA, D=E∩P, and S_a,S_c the labelled descendant fragments still connected to a,c after E.

The sharper hypothesis is needed only when |D|=1: if the detached endpoint fragment and outside labels in u's component are both nonempty, u's component must also contain an endpoint label. Requiring both S_a and S_c nonempty implies this hypothesis. Normalize by removing D and, only when |D|≥2 and u has a parent, adjoining its actual incoming edge e_u.

The E2 hypothesis eliminates every labelled attachment from the interiors of the corridor. The only labels that restoration can connect are S_a, S_c, and labels W reaching the corridor through u's parent. Endpoint fragments include their stems from the endpoint root to retained labels. Those stems are disjoint from every other component embedding within the endpoint subtree: another component cannot intersect a connected fragment in the original deletion forest, and the equality of the whole endpoint subtrees transfers this fact to F1.

If D is empty, nothing changes. With one cut and no outside labels, the two endpoint fragments join within their common pendant clade. Their labelled restrictions agree in the two forests. Any outside component embedding stays outside that clade, and the stem observation excludes every detached component inside it. If the detached fragment is empty, no labelled component changes. In the remaining one-cut case, the anchor hypothesis gives an endpoint fragment on the u-side. Its existing component already connects that fragment to W. Replacing this pendant fragment by the sibling join with the detached fragment preserves its rooted restriction. The existing embedding already occupies the common parent in F1; the only new vertices lie on the detached endpoint's stem and fragment, which no other component uses.

With at least two cuts, adding e_u separates W whenever it exists; at a component root W is empty. The changed blocks are S_a∪S_c and W, with empty blocks discarded. The first is the join inside the common pendant clade. The second is a restriction of an old component. Their embeddings are disjoint from each other and the unchanged components for the reasons just given. Thus every new block has the same rooted restriction in both forests and the minimal embeddings remain disjoint. Cutting incoming edges of the block embedding roots realizes this partition, so the result is an AF.

Since e_u is outside P, the exact current-edge count is

    |N(E)| = |E| - |D| + δ,

where δ=1 exactly when |D|≥2, e_u exists, and e_u∉E\D. Otherwise δ=0. This proves count nonincrease and handles the missing-parent case without an invented edge. Semantic composition of forests transfers the AF to T1,T2; that statement alone supplies no equality of original cutsets.

## Minimum fragments

Let A be an identical proper pendant subtree in two current binary forests and let v be its root. Suppose an AF cutset E leaves no A-label connected to v. Every component containing an A-label is then entirely inside A. Restore every internal A-edge in E and cut the incoming edge of A. The resulting A-component is the entire common subtree, and all outside label blocks are unchanged. Outside embeddings cannot enter a pendant subtree containing none of their labels. Consequently the replacement is an AF.

A labelled leaf cannot have an empty root fragment. At an internal binary root, each of its disjoint child branches contains a label. Emptying the root requires at least one cut in each child branch, hence at least two internal cuts. Restoring all such cuts and inserting at most one incoming edge decreases the cut count strictly. A globally minimum current-forest AF cutset therefore has a nonempty root fragment in every proper common pendant subtree. The argument does not apply to a minimum constrained to retain those internal cuts. EmptyRoot.lean checks the binary cut lower bound and strict arithmetic inequality; the AF replacement in this paragraph is the prose argument.

## Two exchanges

Assume the exact common-uncle geometry in Lemma6.10: the a–c path has exactly two pendant nodes with incoming edges P={e_b1,e_b2}; x is a common subtree, sibling of the common a/c parent in F1 and sibling of u in F2. Start from a global minimum E0 in the current F2, with at least one path cut and at least two cuts among P, the a–c path, and Q={e_x,e_u}. These are explicit starting premises. Existence of such an E0 from the earlier sequential branch equalities still requires the branch-cut transport argument.

Minimum-fragment survival applies to A,C,X. Adding P changes none of their internal edges. The first full normalization preserves all three fragments and joins the surviving A,C fragments at u. The resulting cutset C1 contains P and no edge of the a–c path. Intermediate minimum status is unnecessary.

The exact second-exchange representation follows from this particular geometry. In G=F2~P, cutting P detaches the whole pendant subtrees. Every suppressed vertex lies strictly on one of the two corridor arms from u to a,c. The vertices a,c,u and p=parent(u) survive: a,c retain their complete endpoint subtrees before the completion cuts, u retains the two corridor arms, and p retains its children u,x. All edges outside those arms and P are unchanged original edges. In particular e_x,e_u and the optional incoming edge of p retain their original identities.

Because C1 has no corridor cut, R=C1\P is literally a set of these unchanged G edges. Cutting R in G and yielding gives exactly the forest obtained by cutting C1 in F2 and yielding. Its cardinality is |C1|-2. The A,C fragments at u and the X fragment persist through suppressing unlabelled corridor vertices. Before R is cut, u is the complete common a/c subtree in G and is a sibling of x. The second normalization therefore applies to the compound pair (x,u), with E2 empty. Its actual path is {e_x,e_u}, and its optional replacement parent is the original incoming edge of p, absent precisely when p is a component root. Adjoining P after this operation yields a cutset on the original current F2 with the same AF and exact additive count.

For the count, put p0=|E0∩P|, s=|E0∩path(a,c)|, q=|E0∩Q|. Let δ be the first genuinely new incoming cut, r the second actual path-cut count, and ε the second genuinely new incoming cut. Then r=q+δ, δ=0 when s=1, ε=0 when r≤1, and the final change is

    2 - p0 - s + δ - r + ε = 2 - p0 - s - q + ε.

If ε=0, p0+s+q≥2 suffices. If ε=1, r≥2. Either δ=0 and q≥2, or δ=1, s≥2 and q≥1. Both give p0+s+q≥3. The change is therefore nonpositive. This uses actual E0 counts and does not infer the source's E′1=E1 from E⊆E0.

This corridor-specific representation is a reviewer-supplied proof supplement. It needs a further independent read before it can complete a multi-pass claim for the entire Lemma6.10 proof. Its finite checks enumerate the five-atomic-label common-uncle geometries and intact compound expansions; they do not prove its universal statement. It does not supply the general protected-origin lifting theorem.

## A2BC exchange

For either chosen endpoint e in {e_a,e_c}, take a global minimum E0 containing e and at least one of the two pendant cuts. The minimum-fragment lemma supplies the two endpoint survivors. Adding both pendant cuts costs at most one. Full path normalization removes at least one cut and adds at most one only when it removes at least two, so it saves at least one cut. The resulting AF cutset contains both pendant edges and has cardinality at most |E0|; global minimality makes its cardinality exactly |E0|.

This establishes the graph Exchange premise for the ordinary and endpoint-swapped protected-c selection at this fixed current forest. It does not equate the resulting set with the source's partial-restoration formula. Existential coverage, old-protection exclusion, and transport to later residual states are separate premises in the conditional Lean consumers.

## General lift still required

For every allowed reduction or promising child of an active forest F, prove that each optimal residual completion r lifts to an optimal original-current-edge cutset s containing the chosen branch cuts, with the required additive cardinality. For a compressed residual edge bearing a protected flag, the lift must be choosable to include the designated protected original edge in that compressed path. Distinct compressed paths and prior cuts must be disjoint. Include the corresponding root-sibling replacement statement. OR-ing protection bits proves none of these graph or optimality assertions.

This general statement is used in deriving raw-edge existential coverage from the source optimum-decrease equalities, constructing E0 after sequential reductions, and preserving exclusion along the promising path. Neither reviewed construction nor the conditional Lean files proves it. No algorithm correctness, running time, convention transfer, or novelty conclusion follows from the local results alone.
