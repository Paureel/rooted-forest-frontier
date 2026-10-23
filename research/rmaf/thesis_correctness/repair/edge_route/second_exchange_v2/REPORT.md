# Specific second-exchange transport, version 2

The bounded adversary found no transport failure. The construction proves exact parent-map commutation and cut-and-yield equality for two explicitly witnessed pendant suppressions, and records the second normalization's precise edge support. There are **26 Lean-checked production lemmas**. The remaining formal interface is the derivation of those two witnesses from the general reduced-binary parent-graph geometry. A direct mathematical derivation is given below for fresh review; it has not been encoded in Lean.

This report concerns the geometry in [SECOND-EXCHANGE-TARGET.md](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/SECOND-EXCHANGE-TARGET.md). It does not prove AF normalization, the source algorithm's global correctness, or its runtime. The fresh review of the earlier edge construction does not cover this new construction.

## Statement and original-edge convention

An edge is identified by its original child vertex, together with its parent endpoint. A suppressed child ID is removed; if suppression redirects a surviving child's parent, that edge is **changed**, even though its child ID remains. No two cutsets are identified because they yield equal label partitions. Original here means the active forest F before B is cut; a reached state may already contain atoms from earlier cherry contractions.

Let F be a finite reduced rooted binary forest. Reduced means that unlabelled unary vertices and unlabelled empty leaves have been removed. Its unlabelled internal vertices have two children; a labelled rho root may be unary. Let a and c be incomparable roots of nonempty descendant subtrees in one component, let u be their LCA, and let x be u's sibling with parent v. The subtree at x is nonempty. Let P be the original a–c edge path. Let B contain exactly the incoming edges of all pendant subtrees attached to internal vertices of that path, with |B|=2. G is the forest obtained by cutting B and yielding. Original vertex IDs and labels are retained on surviving vertices.

For an original-edge cutset K with B subset K and K disjoint P, set C=K minus B. The desired local transport is:

- Every edge of C is an actual edge of G with its original ID and parent endpoint.
- Yield(G minus C) equals yield(F minus K), retaining the same surviving IDs, parent endpoints, labels and rooted component structure.
- The label fragment connected to x, respectively u, agrees between the two cut forests; the descendant-root fragments also agree.
- |K|=2+|C|.

The second path in G is exactly {ex,eu}, where these are the original edges entering x and u. Its LCA is v. For the root-safe rule, let D=C intersect {ex,eu}. Remove D and add the original incoming edge of v exactly when |D|=2 and that edge exists. Call the result C'. Then C' has literal original-edge provenance, is disjoint from B union P, and K'=B union C' satisfies the same transport and |K'|=2+|C'|.

The equality here compares G minus C' with F minus K'. It does **not** claim the normalized forest equals the forest before normalization.

## Geometry and transport argument

1. Every proper internal vertex on either descending arm from u to a or c has one path child and one off-path child. The off-path child roots one pendant subtree. The LCA u has both children on the path. Binary validity therefore puts the two elements of B at exactly two proper arm vertices, s1 and s2. They are unlabelled. They can be on different arms or on the same arm.

2. Cutting B makes just s1 and s2 unary in the component containing u. If they are on one arm, suppress the endpoint-nearest one first. In a local suppression of s with its sole remaining child t, remove s and replace the parent of t by the former parent of s. Both original incoming IDs s and t lie in P. The second suppression may reuse the same continuing-child ID t. All vertices of the two detached pendant subtrees retain their structure. Nonempty a/c subtrees ensure u still has two descendant arms; nonempty x ensures v still has both children u and x. Thus x,u,v survive yielding F minus B. Nothing outside B union P changes. In particular ex,eu and the incoming edge of v, when present, retain both endpoints; a missing incoming edge remains missing.

3. Residual cuts C avoid both suppressed IDs and both continuing-child IDs, because these lie in P. A cut outside these incidences commutes with each local parent-map rewrite. This is exact function equality in `two_splices_cut_commute`; it is not inferred from partition equality. Consequently the raw parent maps obtained by cutting C after the two rewrites or by cutting B union C before the rewrites agree, apart from the deliberately removed unlabelled vertices.

4. Suppression remains valid for the final yielded forest even if residual cuts remove every labelled descendant of a continuing subtree. The recursive evaluator proves this without a nonempty-fragment hypothesis: a cut pendant yields its own complete forest; an uncut unlabelled parent with only the continuing side collapses to that side, including when it evaluates to empty. `two_splice_yield` proves that the complete resulting forest is the target component forest plus the two detached pendant forests with all their residual cuts. The counted component trees retain node IDs, labels and child orientation, so the equality is stronger than equality of unlabelled partitions. Other input components are identical on the two sides and can be added to both forest bags.

5. For a raw component label fragment at x or u, each suppression replaces the two-edge route through an unlabelled degree-two vertex by one edge. It preserves connectivity among every other vertex, hence among x/u and all labelled vertices. Cuts C do not remove either edge of that route. This also applies when the incoming edge of x or u is cut. For a descendant-root fragment, restrict to the original subtree at that vertex and ignore its incoming cut. The subtree at x is unchanged. The subtree at u has the same two local suppressions. The Lean `two_splice_root_component` theorem proves equality of the attached root component in the explicit tree representation. It does not require the fragment to be nonempty.

6. In G the edges ex and eu meet at v and form the full x–u path. All three possible modified IDs ex,eu and the incoming edge of v lie outside B union P. Hence the second rule leaves every suppressed corridor incidence uncut. `SecondCut.lean` proves its exact support, removal of both path cuts, literal provenance of every retained/added cut, and absence of any addition when v has no parent. The same two-splice transport applies to C'. Finally B is disjoint from C and C', so the literal lift adds exactly two distinct edges. `lift_exact_count` and `lift_nodup` record that list/set accounting.

Steps 1–2 and the conversion from parent graphs to the recursive tree representation are the **remaining formal interface**. The Lean result does not silently assume their conclusion as a theorem about arbitrary graphs.

## Smallest remaining formal graph lemma

Given precisely the finite reduced binary geometry above, construct an original-ID marked-tree encoding of the component containing u and two `PendantSplice` witnesses, ordered from the endpoint upwards if nested, such that:

- their two deleted unlabelled vertices and their continuing-child incidence IDs belong to P;
- their pendant roots are the distinct original B edges;
- the target tree together with the two detached pendant trees encodes G, and x,u,v are unchanged IDs outside the splice incidences;
- every residual edge marking C disjoint from B union P induces the same two witnesses, with identical marks on retained original IDs; this holds also in the subtree at u with its incoming mark cleared;
- the encoding's recursive cut evaluator represents the graph's labelled yielded forest and descendant-root fragment.

This is a geometry-to-certificate and representation lemma, not an AF lemma and not an assumed general suppression/cut commutation theorem. Once supplied, the compiled local results give the requested exact yield transport and the second normalized lift. The argument above supplies a proposed mathematical proof of its structural part. Universal graph-level formal closure remains open pending that encoding and fresh review. The raw whole-component fragment argument in step 5 is also a prose connectivity argument; its graph-to-evaluator correspondence is not separately encoded in Lean.

## Executed adversary controls

The [frozen input](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/second_exchange_v2/two-stage-original-spec-frozen.json) was read as data. The reused independent graph oracle reran its four prior fixed controls before the new controls and before each reached-state search. Outputs were redirected into this v2 directory, preserving prior receipts.

The concrete trees are T1=(((a,c),x),(b1,b2)) and T2=((((a,b1),b2),c),x), each with labelled rho. Independent exhaustive original-cut enumeration gives optimum 2. Both starting cutsets produce AFs, both intermediate forests are AFs, and both final forests are AFs:

| Starting original edges | First normalized K | Residual C in G | Second residual C' | Lifted K' | Counts |
|---|---|---|---|---|---|
| {ea,ec}={5,8} | {2,6,7} | {2} | empty | {6,7} | 2 → 3 → 2 |
| {ea,ex}={5,9} | {6,7,9} | {9} | empty | {6,7} | 2 → 3 → 2 |

Here a=5,c=8,x=9,u=2,v=1; B={6,7}, P={3,4,5,8}. G removes IDs 3 and 4 and changes edge 5's parent from 4 to 2. Original ex=9→1, eu=2→1, and the incoming edge 1→0 are unchanged. The planted assertion that edge 3→2 remains unchanged is rejected. Removing either member of the final B fails the AF check.

Detaching rho from both corresponding source components leaves v as an unlabelled root. All four possible residual cutsets outside B union P pass transport and second-lift checks. The optional incoming edge of v is absent in all four. These are controlled structural variants; they are not evidence of algorithmic reachability. See the [complete control receipt](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-edge-second-controls.json).

## Bounded reached-state evidence

The original algorithm is used only to generate call states and identify its 2B branch. The checker derives paths, pendants, cuts, yielding, fragments and endpoint maps from the independent graph oracle. It does not use the algorithm's cut/reduce/shape routines as an AF checker. No component-route code or report was imported.

Twenty-input pilots at n=5 and n=6 took 0.025 and 0.036 seconds and found zero 2B states. They contributed no transport evidence. Projections were recorded before extending. Seed 622 and all budgets 0 through n−1 were retained in the bounded extensions:

| n | Ordered input pairs | Distinct reached 2B contexts | K premises | Second lifted premises | v-root contexts | Measured seconds |
|---|---:|---:|---:|---:|---:|---:|
| 5 | 3,000 | 149 | 1,192 | 1,192 | 0 | 3.633 |
| 6 | 2,000 | 179 | 3,256 | 3,256 | 0 | 5.465 |

The retained-context key includes the source pair, active parent/label dictionaries and a,c,x. Thus 328 is a context count, not a claim of 328 nonisomorphic forests. Every allowable K was enumerated in each retained context. All 4,448 K transports and all 4,448 second lifts passed exact final node-ID/parent/label equality and both fragment checks. Root-v reached premises are **zero**; the four detached-rho controls supply the only root-v transport tests in this v2 work. There is no universal conclusion from this sample.

Receipts: [n=5](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-edge-second-reached-n5-limit3000.json), [n=6](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-edge-second-reached-n6-limit2000.json).

## Formal verification and provenance

[ParentTransport.lean](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/second_exchange_v2/ParentTransport.lean) proves eight parent-map/provenance/count facts. [YieldTransport.lean](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/second_exchange_v2/YieldTransport.lean) proves thirteen recursive evaluator/context/splice facts. [SecondCut.lean](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/thesis_correctness/repair/edge_route/second_exchange_v2/SecondCut.lean) proves five exact second-rule facts. The concrete controls include both rho-presence states, both u-cut states, the parent-present/absent rule and the one-cut rule. The deliberately false retained-corridor assertion fails compilation.

The isolated audit rebuilt every local production import in a separate output directory and recorded actual return codes. Production and positive sources compile; the negative control fails for its false proposition. Only `propext` and `Quot.sound` occur in the printed axiom dependencies. No admitted proofs, custom axioms or native evaluation tactics were used. The [formal receipt](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-edge-second-formal-audit.json) records commands, timings, source hashes and logs. Earlier v1 production/control hashes and the frozen input/oracle hashes were rechecked unchanged.

The Python checker reuses the earlier independently written original-edge oracle. It is an independent implementation relative to the algorithm's state generator, but its reuse is not a second independent oracle. The Lean proof was authored in this route after the adversary controls and is awaiting a new nonauthor review.

The interface to the first exchange is exactly K intersect P=empty, supplied by full path-set normalization. No equivalence with the thesis's partial path restoration is asserted here. AF preservation and minimality-to-fragment arguments remain separate obligations. This v2 work does not change the earlier compound-endpoint counterexample or its scope.

The repository-wide `./bootloops-check` suite was not run in this v2 scope: no shared toolkit implementation was changed. The relevant controls, bounded searches and isolated Lean compilations were executed as recorded. The geometry-to-certificate formalization and a new nonauthor review are unfinished.
