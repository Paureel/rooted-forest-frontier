# Triple-component terminal completion: proof and open formal interfaces

Status: handwritten argument with finite adversarial support; full theorem acceptance remains **OPEN**. The recurrence and characterization were retrieved from the previous note, Section 6. This document expands their proof obligations; it does not claim an independent discovery or a new unrestricted exponential bound.

## Statement and conventions

Let T be a rooted binary tree on n distinctly labelled leaves. Let F be a rooted binary source forest with m nonempty components whose leaf sets partition the same labels. Every source component D is either isomorphic to T restricted to its labels, or has exactly three labels. A completion is a leaf partition refining the source components, with equal rooted restrictions on every block and pairwise vertex-disjoint minimal spanning embeddings in T and separately in every D. There is no added rho label and no acyclicity constraint.

The proposed terminal solver minimizes the final number p of blocks. Its additional-cut count is p−m. Starting from a single source tree, if r nonredundant source cuts have already been paid, m=r+1 and the total is r+(p−m)=p−1. Empty unlabeled pieces are discarded. A forest with disjoint nonempty labelled spans can be realized by p−m cuts: extend the spans across unassigned vertices within each source component until all vertices belong to a nonempty region, then cut the region boundaries. A finite tree with p_i connected regions has p_i−1 boundary edges. The general graph proof of this cut-realization fact is not formalized in this route.

## Characterization and source disjointness

Give every leaf the color of its source component. A color is bad exactly when its three-leaf source tree disagrees with the target restriction. The claimed characterization is:

A leaf partition is a completion if and only if its blocks are monochromatic, its target spans are pairwise vertex-disjoint, and no block equals all three leaves of a bad color.

Necessity follows directly from refinement, target disjointness, and incompatible full-triple topology. For sufficiency, fix one source color.

For a good color with label set L, D is isomorphic to the suppression of the minimal target subtree S=T[L]. Every block B⊆L has the same rooted restriction in D and T: restricting to L and then B is equivalent to restricting directly to B. To transfer disjointness, examine each maximal subdivided edge of S. Its interior vertices are unlabeled and have one parent and one child in S. A minimal span of labels B⊆L cannot end at an interior vertex: its extremities are selected leaves or the branching LCA of at least two selected leaves. Consequently, if that span uses the interior of a subdivided edge, it uses the whole edge-path including both retained endpoints. Suppression therefore cannot turn disjoint spans into intersecting spans. An intersection after suppression either occurs at a retained vertex, already shared before suppression, or uses a retained edge, whose original endpoint vertices were already shared. Root suppression causes no exception: the root of the minimal subtree S is its labels' LCA and is retained unless S is a singleton. The rooted isomorphism to D now transfers disjoint spans and restricted topologies. This explains why closed good-color regions need no further source-history state.

For a bad triple, any proper partition is either a pair plus the remaining singleton, or three singletons. A rooted two-leaf restriction has unique labelled topology. A leaf not selected in a pair cannot be an internal vertex on the pair's path, because it has degree one. Thus the singleton is disjoint from the pair span in every source topology, and three singleton spans are disjoint. No other proper partitions exist. Source regions belonging to different colors are in different source components. This explains why a bad color requires only its open leaf subset, without the already closed subsets.

**Precise formal debt G1:** prove composition of rooted restriction and invariance of pairwise minimal-span intersection under suppression of subdivided edges, with the singleton and root cases included. Neither the Python enumeration nor the generic Lean table theorem supplies G1. The existing `RMAF.lean` executable restriction/minimalVertices model still has its separately recorded graph correspondence debt.

## Region normal form and recurrence

A collection of disjoint connected vertex regions containing all labelled leaves induces a target-disjoint leaf partition by taking each region's labels and trimming to its minimal span. Conversely, the minimal spans of a target-disjoint partition are already such regions; unused vertices are permitted. Therefore it suffices to minimize nonempty connected regions subject to monochromatic labels and the bad-triple prohibition.

At a vertex v, at most one region contains v. An open region is the region that contains v and may extend through the parent edge; all other nonempty regions below v are closed. A region that enters a rooted child subtree but contains no leaf there can be trimmed out of that child: a minimal connected span cannot enter and leave a one-edge attachment without a terminal leaf. We may thus require every open region to have a nonempty label set below its boundary.

Use state None if v is unused. An active state is (i,0) for a good color i, or (i,S) for one of the six nonempty proper subsets S of a bad triple. A table value counts closed nonempty regions; an open region is not yet charged. Leaves have only their own singleton active state at cost zero.

For a child w let C_w be the minimum of its None cost and each active cost plus one. At an internal binary vertex, the exhaustive choices are:

1. v is unused: close both children, costing C_l+C_r.
2. The root region meets only the left child: extend that child's active state and close the right child.
3. The symmetric right extension.
4. The root region meets both children: join the two child regions, which must have the same color, and require their bad masks to have disjoint union of size at most two.

A connected region meeting both child subtrees contains v. Conversely, each listed join/extension constructs disjoint connected regions, with disjoint child vertex sets and a single region using v. Rooted child configurations of the same boundary state can be replaced by cheaper ones: future transitions use only the state and add nonnegative closed-region charges. Thus induction yields exactness of the minimum table. At the root close its remaining active region, if any.

For a bad color, a permitted two-child join must combine two distinct singleton masks. There are exactly six ordered possibilities. Two child subsets cannot repeat a bad leaf because target labels are unique. A pair mask plus any disjoint nonempty mask would be the forbidden full triple.

Adjacent regions with the same color sometimes must remain separate. For T=((a,b),c) and D=((a,c),b), the regions containing {a,b} and {c} form a valid two-block solution. Extend the first region to the target root; it becomes adjacent to the singleton c. Merging produces the incompatible full triple. The frozen comparator and Lean finite mask control both reject value one.

**Precise formal debt G2:** define valid disjoint connected region families on all binary-tree vertices and prove their restriction/assembly bijection with the four transition forms, including the elimination of leafless boundary regions. The Lean LCA lemmas establish necessary crossing and child-restriction facts, not this entire bijection.

**Precise formal debt G3:** instantiate the generic automaton theorem for arbitrary good/bad color sets and prove that the factorized Python table and backpointers implement that instance. The generic theorem proves exact minima over the specified transition derivations, not automatically over graph agreement forests.

## Exact core operation and reconstruction counts

Let g be the number of good colors and b the number of bad colors, with g+b=m. The full table width is K=1+g+6b, even if some states are unreachable at a vertex. Precomputed joins number J=g+6b. At each internal vertex the code attempts exactly

    1 + 2(K−1) + J = 1 + 3g + 18b

candidate transitions. It scans 2K entries to choose the two child closing minima. A rooted binary tree with n leaves has 2n−1 vertices and n−1 internal vertices. The code stores (2n−1)K scalar values and equally many backpointer slots, attempts (n−1)(1+3g+18b) transitions, performs 2(n−1)K child-closing evaluations, and performs K final root evaluations. Array initialization also costs O(nK). This is O(nm) time and memory on a word RAM with counts and vertex/state indices fitting O(log(nm)) bits. It is not a unit-cost arbitrary-precision bit complexity claim.

Backtracking assigns a fresh integer region identifier when an active child is closed, and passes the current identifier through selected extensions/joins. It visits each target vertex exactly once, assigns each labelled leaf once, and appends each leaf to its output block once. It therefore takes O(n) time and output space in label references after the tables, with no repeated leaf-set copying. Serializing string labels additionally costs their total byte length. The Python counters assert 2n−1 backtracking visits. Input parsing, class validation, canonical shape comparison, and the separate witness checker are polynomial preprocessing/verification costs outside the O(nm) core claim. The research implementation is recursive and subject to the Python recursion limit on sufficiently deep trees; no arbitrary-depth software support is claimed.

The Lean file proves the count identity and linear inequalities. It does not extract a machine-code runtime bound or verify the Python implementation. The retained counters check the stated counts on executed cases.

## Reachable baseline child; no pre-cutting reduction

The locally read baseline text, PDF pp.17–18, Branching rule 4, branch 2, instructs the solver to cut off a. For T=((a,b),(c,d)) and T'=((a,c),(b,d)), the target cherry {a,b} has the two source pendant taxa c,d, with {a,c} a source cherry. There is no common cherry and no one-pendant cherry path, including the symmetric tree orientation. Rule 4 applies. Its a-cut child is F={a, (c,(b,d))}. The remaining three-label component is incompatible with T restricted to {b,c,d}, so this is a triple terminal instance. Tidying away the singleton leaves the incompatible three-leaf pair and retains its already-paid cut in the budget.

`large_checks.py` checks that the child is an actual source edge-cut forest, that its completion takes one additional cut, and that both the original pair and this child have final optimum three components. This is a post-hoc illustrative example, not a fresh acceptance fixture. The detector can be evaluated at an existing baseline recursion node; there is no permission to make arbitrary cuts merely to enter the class. No proof is supplied that terminal nodes cover every optimum, occur often enough to improve a worst-case recurrence, or provide a safe cover.

## Evidence and acceptance boundary

The independent-core graph edge-cut census and scalar DP share an author, raw input conventions, Python, and the interpretation of the definition. They share no implementation primitives. The frozen controls ran before the census, and no solver change was made in response to a census discrepancy. All 9,660 five-leaf class instances and all 8,505 fixed two-triple six-leaf instances passed optimum, witness, and partition-by-partition characterization checks. The source note's counts were visible before construction, so reproducing those counts is not held-out evidence. The full source hash used by the census is preserved as `cut_oracle-census-v1.py`.

Lean 4.35.0 checks 28 stated theorems: generic table optimality/infeasibility, min-sum factorization, exact bad-mask joins, address-boundary lemmas, operation arithmetic, canonical triple controls, proper partitions for arbitrary distinct labels in all three representative rooted shapes, the full-triple topology test, and one/two/three-leaf tree structure. The latter deliberately share `RMAF.lean` semantics. The destructive wrong-cost file fails compilation. Audits permit only propext, Classical.choice, and Quot.sound and find no custom axioms or proof placeholders in the accepted sources.

The 60- and 600-leaf scale cases have independently checked witnesses only; their DP values are not independently certified optima. The larger case uses 200 colors, of which 134 are bad, and has 1,199 backtracking visits. Its timing is an environment-specific observation, not a speed record.

A fresh-author verifier was launched after the implementation, with instructions to freeze a separate partition/triple/path oracle before reading the DP. Its results must be assessed separately when available. Until G1–G3, graph semantics, and the fresh verification gate are discharged, the terminal theorem is not graded VERIFIED-CLOSED. The unrestricted sub-2.3391 target remains open, and Whidden's 2013 base-two prior art still requires reconciliation.
