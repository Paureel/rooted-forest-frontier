# Second independent review of the local normalization and two-exchange argument

The restricted normalization, strict empty-common-subtree repair, and corridor-specific transport form a sound **reviewed prose local argument** under the explicit current-forest hypotheses below. The original and version 2 Lean files rebuilt and establish their stated combinatorial, arithmetic and conditional results. They do not provide a kernel-checked agreement-forest theorem for arbitrary parent graphs. General optimum lifting, protected-origin lifting, later root-sibling transport, marked-state induction, algorithm correctness, runtime and convention transfer remain outside this conclusion.

The review found no counterexample to the restricted local argument. It independently reproduced the compound-empty and partial-restoration failures of broader statements. Neither failure is a counterexample to a minimum-cutset consumer: their cut counts are respectively three and two, while both instances have optimum one.

## Exact theorem accepted in prose

Use finite reduced rooted binary forests with the thesis's labelled unary rho convention. Let F1,F2 be yielded forests of T1,T2 on the same labels, with every F2 label block contained in an F1 block. The complete proper pendant subtrees A,C rooted at a,c agree in the current forests before further cuts; a,c are siblings in F1 and connected in F2. Let E consist of actual current F2 edges and yield an AF of F1,F2. Require E2 subset E to preserve A,C intact and make a,c siblings after yielding. Write P for the a-c path, u for its LCA, and D=E intersect P.

When |D|=1, require the following anchor: if the endpoint fragment detached from u has a label and u's component contains an outside label, then u's component contains an A or C label. No survivor condition is required for |D| different from one. Remove all D and add eu only if |D| is at least two and u has an actual parent. The resulting cutset N(E) yields an AF and satisfies

    |N(E)| = |E| - |D| + delta,

where delta is one exactly when that parent cut is genuinely new, and zero otherwise. In particular, the count does not increase. Both endpoint root fragments surviving is a sufficient stronger hypothesis; an endpoint may be compound and internally cut.

The proof needs the entire stems from a,c to their surviving labels. Those stems are disjoint from every detached component inside their identical endpoint subtrees. In the one-cut case with outside labels, the anchor's old component already passes through the common parent in F1. Joining the detached endpoint fragment only extends this embedding along the other endpoint stem. With at least two cuts, eu separates the outside labels; if eu is absent, the outside fragment is empty. The remaining components have compatible rooted restrictions and disjoint minimal embeddings. This proves AF preservation by the cut-forest partition criterion, including rho-containing components. It does not identify original cutsets from equal label partitions.

For an identical proper common subtree rooted at v, an AF cutset that leaves v disconnected from every descendant label admits a strict repair: restore every cut strictly inside that subtree and cut ev. At least two internal cuts were necessary, one in each binary child branch; at most one incoming cut is inserted. All outside label blocks remain unchanged, and the whole common subtree is a valid new component. Consequently a globally minimum AF cutset on the current F2 leaves a nonempty root fragment at every such v. Minimum among forced extensions or inclusion-minimality is insufficient.

## Independent transport reconstruction

Before reading any proof report, I wrote [INDEPENDENT-DERIVATION.md](INDEPENDENT-DERIVATION.md) and a new graph evaluator. For the common-uncle geometry, let x be u's original sibling, v their parent, and B the two pendant edges at internal vertices of P. Exactly two non-LCA internal corridor vertices have an off-path child. Cutting B makes these two vertices unary; nonempty endpoint and x subtrees keep a,c,u,x,v present in G=yield(F2-B). Every changed non-B edge lies on P.

For **any** K containing B and avoiding P, C=K-B therefore consists of unchanged actual G edges. The two unary substitutions commute with deleting C because C cuts none of their incident corridor arcs. Later empty fragments cause no difficulty: contraction of an uncut unary vertex preserves all connections among the remaining vertices, even if no label remains below it. Yield(F2-K) and yield(G-C) have the same surviving vertices, labels and rooted edges. Descendant root fragments and whole-component label sets at u,x agree. The exact cardinality is |K|=2+|C|.

The x-u path in G consists literally of the original ex and eu. The optional incoming edge of v also has its original endpoints, or remains absent. Full second normalization changes only these edges and so introduces no corridor cut. Its residual C' lifts as K'=B union C', with the same yield, fragments and exact count 2+|C'|. No AF or optimality premise is needed for this transport lemma. The AF conclusions require the separately reviewed normalization theorem.

The first reviewer's new supplement agrees with this independently recorded argument. It correctly requires full first-path restoration and does not invoke optimality of the intermediate cutset. This second review covers that supplement as prose.

## Consumer rulings

| Use site | Ruling and precise requirement |
|---|---|
| Thesis Lemma 6.5, printed pp.101-103 | The arbitrary compound statement lacks the required one-cut anchor. The executed three-cut example fails normalization despite active AF compatibility. Use the restricted theorem above. |
| Lemma 6.10, pp.112-113: starting E0 | A global minimum current-edge E0 with at least one P cut and at least two cuts in B union P union {ex,eu} is an explicit input. Its existence from the earlier sequential branch equalities still requires the general optimum lift. |
| Lemma 6.10: first exchange | Minimum survival applies to A,C,X before adding B. Adding B and full normalization leave their internal cuts unchanged. The actual operation restores all E0 path cuts, not merely the source's selected E3. |
| Lemma 6.10: second exchange | The first restoration joins surviving A,C fragments at u and preserves X's fragment. In G, u is the full common sibling join before the residual cuts. Transport above supplies actual G edges and the path {ex,eu}. Intermediate minimality and ordinary-leaf status of u are unnecessary. |
| Lemma 6.10: count | With p=|E0 intersect B|, s=|E0 intersect P|, q=|E0 intersect {ex,eu}|, first insertion delta, actual second-path count r=q+delta and second insertion epsilon, the final difference is 2-p-s+delta-r+epsilon. If epsilon=0, p+s+q at least two suffices. Otherwise r at least two forces p+s+q at least three. The final AF cutset contains B and is minimum by comparison with E0. |
| Thesis p.113 equality E1'=E1 | E subset E0 does not justify equality of their intersections with {ex,eu}. The repaired count uses actual E0 intersections. No in-regime numerical counterexample to that source equality is claimed by this review. |
| Theorem 6.12, p.116: ordinary A2BC exchange | From a global minimum E0 containing ec and at least one B edge, adding B costs at most one and full normalization saves at least one. It produces a minimum AF cutset containing both B edges. It need not be the source's partial-restoration set E0 minus {ec} union B. |
| Protected-c endpoint swap | Interchanging a,c proves the same fixed-current-forest exchange with ea. This supplies exactly the Exchange predicate assumed by protected_c_existential_branch. Coverage and exclusion of old protections remain premises. |
| BCY and inherited exclusion | Rebuilt conditional implications are valid. Their raw-edge coverage and lifting predicates are not forest theorems established here. |

The two-exchange result gives a minimum original-current-edge cutset containing B and a corresponding AF residual of size |E0|-2 in G. This review does not promote that construction to a general equality of residual optima: converting arbitrary optimal residual completions back to original current edges is part of the remaining general lift.

## Executed evidence

The new checker imports only Python's standard library. It enumerates F1 cut-yields to test AF membership and reduces F2 graphs explicitly while retaining original-edge path provenance. This differs from the prior review's minimal-hull/embedding evaluator, whose code was never read or imported. The shared inputs are the pinned theorem statements, primary source conventions and frozen fixtures. Those shared inputs limit independence for transcription errors; the source pages were read directly to address that risk.

Controls ran before the target reconstruction. Identical trees returned optimum zero, a known one-rearrangement pair returned optimum one, zero cuts retained the original reduced edges, and cutting every edge yielded singleton labels. A wrong topology and a false unchanged-edge claim were rejected. Each production assertion compares exact sets or tuples; no floating tolerance enters a mathematical result.

For the frozen 2B fixture, original IDs are path-based and enter their named child vertices. Here u=n0, v=n, x=n1, B={e:n0001,e:n001}, ex=e:n1 and eu=e:n0. The optional incoming edge is e:n from rho to n. The first arm becomes a concatenated edge from n0 to a=n0000; the suppressed edge e:n00 is absent, so the deliberately corrupted unchanged-edge assertion fails.

| Frozen initial cutset | First normalized cutset | Final cutset | Counts |
|---|---|---|---|
| {ea,ec}={e:n0000,e:n01} | {e:n0,e:n0001,e:n001} | {e:n0001,e:n001} | 2,3,2 |
| {ea,ex}={e:n0000,e:n1} | {e:n0001,e:n001,e:n1} | {e:n0001,e:n001} | 2,3,2 |

All three cut-yields in each row are actual AFs, and the original optimum is two. Both rows also pass with rho detached as a retained singleton and with the unlabelled component considered alone. The incoming edge of v is absent in those variants. Deleting either final B cut fails the AF test.

| Finite family | Executed scope and result |
|---|---|
| Arbitrary-K corridor geometry | 15,600 cases over 36 graphs, with three arm allocations, atomic or compound A,C,X, optional outside context and three root conventions. All transport and second-lift assertions passed, including exact final surviving IDs/endpoints. 4,560 cases had an empty u or x root fragment. |
| Cuts inside detached pendant subtrees | 16,384 cases; 15,360 cut an internal pendant edge. All exact graph, fragment and count comparisons passed. |
| Four-leaf local normalization/repair | All 225 ordered tree pairs, 675 compatible whole/rho-detached active pairs, 51,516 AF cutsets. All 44,862 N_anchor applications passed, including 43,755 nonminimum applications and 42,204 two-survivor applications. All 5,070 strict repairs and 9,897 minimum-fragment checks passed. |
| Five-label consumer family | 90 fixed active-pair cases; 36 ordinary-c and 36 swapped-a optimum exchanges passed. There were 38 eligible two-stage minimum cases, each with counts 2,3,2. The four-leaf family had zero eligible consumer-exchange cases, so it supplies no such evidence. |

These finite families are not proofs and are not algorithm reachability censuses. The exact tested families, counts, witnesses and elapsed times are retained in the adjacent JSON receipts. The supplemental pendant-internal run was bounded but was not separately piloted at its larger input size; it completed in 5.213492082999437 seconds. The principal geometry, local-normalization and consumer families had recorded pilots before extension.

## Formal scope and version 2 comparison

Eight unchanged original positive Lean modules rebuilt locally; both false controls failed compilation for their false propositions. The modules establish original-edge membership/count and walk statements, ranked-parent path facts, binary empty-root cut bounds, scalar exchange inequalities, and conditional existential/protection implications. The graph boundary conditions, binary encoding and AF preservation are not inferred from compilation. Dependency reports contain only propext, Classical.choice and Quot.sound or no axioms. The source scan found no sorry, admit, custom axiom or native_decide.

Version 2 was read only after its completed summary receipt became available and after my independent derivation and initial 15,600-case transport run. Its four positive modules rebuilt unchanged, and its deliberately false retained-corridor control was rejected. I also printed the dependencies of the two named splice controls omitted from its original print list. The version 2 mathematical argument agrees with the reviewed corridor transport.

The version 2 formal result concerns two explicitly witnessed PendantSplice transformations in a recursive marked-tree evaluator, parent-map commutation under uncut-incidence premises, and second-rule support. Its remaining formal interface is substantial and precise: encode each valid binary parent graph with unique original IDs, derive the two splice witnesses, relate the evaluator to graph yield, and relate attached components to graph root fragments. Whole-component connectivity is a prose argument. The successful rebuild does not remove these hypotheses.

## Smallest remaining general obligation

For each allowed reduction or promising child G of an active forest F, prove that an optimal residual completion R lifts to a current-F cutset K containing the selected branch cuts, yielding the same AF, with the required additive cardinality and global minimum status. If a compressed residual edge carries a protected original edge, prove that a lift cutting that residual edge can select the designated protected origin. The compressed paths and prior cuts must have the required disjointness, and later root-sibling replacement must preserve this correspondence. This is needed to derive raw-edge existential coverage, construct the initial E0 after sequential branches, and preserve exclusion along a promising path. The corridor-specific proof covers only its stated fixed geometry.

Primary-source reading covered printed pp.12-18, 101-103 and 112-116 of the retained July 2013 Whidden thesis. Pages 102,113,116 were rendered from the PDF and visually checked, including the anchor sentence, selected-set equalities and final partial formula. The [source ledger](source-ledger.json) retains exact extracts and hashes. No bibliography entry or novelty claim was added. No general literature or bibliography audit was performed.

All output is local and confined to the assigned review paths. Author proofs, earlier receipts and aggregate theorem counts were not edited. The repository-wide bootloops-check suite was not run; the executed checks are the fresh exact programs and isolated Lean rebuilds described here. BootLoops Python lacks fitz, so primary-page rendering used the bundled Poppler executable.
