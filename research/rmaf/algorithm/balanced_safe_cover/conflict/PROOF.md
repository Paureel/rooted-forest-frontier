# GLOBAL-C constituents and open generation theorem

Status: handwritten source-model arguments, finite exact tests, and kernel-checked abstract combinatorics. The complete smaller-base algorithm remains open. A fresh nonauthor must review the source-tree arguments and their use by the algorithm. These constituents carry no novelty claim.

## Definitions

S and T are rooted binary trees on identical distinct labels, without an added rho. Edges and vertices below are the original unsuppressed trees. For two distinct leaves a,b, P_S(a,b) is the unique undirected source path, including both endpoints, and E_S(a,b) its edge set. For three leaves A, E_S(A) is the union of the three pair-path edge sets. A source cutset C yields the partition P_C of labels by connected components of S-C; unlabeled components are discarded.

Define H(S,T) as the following family of nonempty source-edge sets:

- E_S({a,b,c}) whenever S|{a,b,c} and T|{a,b,c} have different rooted topology.
- E_S(a,b) union E_S(c,d) for four distinct labels, whenever P_S(a,b) and P_S(c,d) are vertex-disjoint, but P_T(a,b) and P_T(c,d) meet.

Duplicates and hyperedges containing another hyperedge may be removed. Both the transversal optimum and the maximum disjoint-packing count stay unchanged: replace a packed larger hyperedge by a contained minimal hyperedge. The implementation retains all distinct hyperedges.

## C1: original cutset characterization

Claim: P_C is an agreement partition exactly when C intersects every member of H(S,T).

Rooted topology sublemma: two rooted binary trees on the same labels agree iff all their rooted three-leaf restrictions agree. For n<=2 there is only one topology. For n>=3 choose a source cherry x,y. It is characterized by xy|z for every other label z: if x,y were not a target cherry, a label in a nontrivial descendant sector at their LCA would instead give xz|y or yz|x. Thus x,y are a common cherry. Contract them to one temporary label in both restrictions. A triple using the temporary label has the same topology as a triple using x and its other two labels before contraction. All other triples are unchanged. Induction gives agreement. The temporary label is for this proof only; original-label reconstruction must expand the cherry if this is implemented as a reduction.

Necessity for a triple constraint: if C misses its span, all three leaves stay in one source component. An agreement block containing them has the same three-leaf restriction in S and T, contradiction.

Necessity for a pair-path constraint: if C misses both paths, each pair lies within a single source component. If the pairs lie in distinct components, their target spans would meet, contradicting target disjointness. If both pairs lie in one component, its source and target restrictions would be isomorphic. Vertex-disjointness of two pair paths is invariant under a tree isomorphism and suppression/subdivision of unlabeled degree-two vertices. Indeed, a subdivided edge belongs to a pair path exactly when that edge separates its two endpoints, and two paths sharing an unsuppressed degree-two vertex must share at least one adjacent path edge unless they terminate there; endpoints here are distinct labeled leaves. Thus source-disjoint and target-intersecting paths cannot lie in one agreeing block either.

Sufficiency: each block B of P_C has a connected source support. If its rooted restriction disagreed with T|B, the topology sublemma would give an incompatible triple inside B. Every edge of that triple's source span survives, so its hyperedge would be missed. Hence each block agrees. Source supports of different blocks are disjoint, being subsets of distinct components of S-C.

If two target supports intersect at v, neither block can be a singleton: a target leaf belonging to one block cannot lie in the support of the other disjoint label set. Each support is the union of pair paths from its block, so choose a,b in one block and c,d in the other whose target paths both contain v. Their source paths lie in disjoint source components. The corresponding pair-path constraint is present, and C misses both paths. Contradiction. Therefore target supports are disjoint, proving agreement.

Source normalization sublemma: if C has r nonempty leaf-bearing components, there is C0 subset C of size r-1 inducing the same leaf partition (size zero for empty input). Contract every component of S-C to one vertex, obtaining a tree with r labeled seeds and possibly unlabeled vertices. Starting at the labeled seeds, assign an adjacent unassigned vertex to any assigned group until all vertices are assigned. Each group remains connected. Contract the r groups; the quotient is a tree on r vertices, so exactly r-1 surviving boundary edges remain. These are original C edges. Thus the minimum cardinality of an H-transversal equals the ordinary agreement-forest cut optimum. No original edge is reinterpreted after suppression, and no empty component is charged.

Constructing H examines O(n^3) triples and 3*binom(n,4) pairings. Explicit paths have O(n) vertices/edges, giving O(n^5) construction and memory; checking a supplied transversal is polynomial. The optimization and cover-size bounds remain separate obligations.

## C2: conflict packing and a saturated witness certificate

If h_1,...,h_p are pairwise edge-disjoint members of H, every transversal contains at least p distinct edges: choose one hit in each h_i; their disjointness makes those choices distinct. `ConflictPacking.lean` proves this for arbitrary finite list families using distinct representatives and a cardinality inequality.

If a supplied cutset K hits every conflict and has exactly p cuts, C1 and this lower bound certify K as an original optimum. Certificate checking is polynomial, including checking that each packed member really is an original triple/path constraint, verifying pairwise disjointness, checking K against H, and normalizing the source cut partition. Finding K or finding a maximum packing is not included for free. The exact maximum-packing routine in `exact_conflicts.py` is a finite test oracle.

Every subset C' of a normalized optimum K is nonredundant: it merges some leaf-bearing final components and creates no unlabeled component. The original optimum P_K refines P_C', so C' safely preserves at least one original optimum. For a component D of S-C', restrict P_K to its labels. These are local agreement pieces and give a witness with at most |K|-|C'| additional cuts. Thus d_D <= |K|-|C'|. More precisely the local witness costs sum to |K|-|C'|. If 2|C'| >= b and |K|<=b, every d_D<=b/2; the arithmetic implication is kernel checked as `halfBudgetFromChargedWitness`.

The terminal predicate still needs checking. Pure overlaps can be verified directly by degrees in the original target embeddings; compatible/triple membership can be verified by restriction equality or component leaf count. Together these checks certify a supplied partial cutset meeting all requirements. Constructing the partial cutset and bounding the number of attempts remain open.

## C3: smallest exact obstruction to packing tightness

Frozen balanced-quartet example: S=((a,b),(c,d)), T=((a,c),(b,d)). Every three-leaf restriction disagrees, so at least one cut is needed; no one-cut partition is an agreement forest. Isolating any two leaves gives a valid two-cut agreement forest, and the exact receipt lists all six optimum partitions. H has four triple-span hyperedges and one source-pair/target-overlap hyperedge. Every two hyperedges intersect, so maximum edge-disjoint packing is one while optimum is two.

The complete n<=3 census contains 11 ordered pairs and no gap; complete n=4 census contains 30 packing gaps among 225 ordered pairs. Thus four labels is the smallest possible gap under these ordinary conventions. The first lexicographic gap in the census is a different caterpillar pair with the same values; both witnesses are retained. This refutes only packing tightness.

## C4: safe global domination of original edges

For an original source edge e define I(e)={h in H:e in h}. If I(e) subset I(f), replacing e by f in a transversal preserves every hit and does not increase its cardinality after duplicate removal. This map is polynomial to compute. `dominancePreservesHitting` proves the universal hit-preservation statement, and `replaceEdgeLength` proves list-length preservation before duplicate removal.

Choose one canonical original edge from every inclusion-maximal nonempty incidence class. For each source edge e with nonempty incidence, select a representative r(e) whose incidence contains I(e); a maximal class exists because the universe is finite. Map any minimum transversal K to the set r(K). It is still a transversal and has cardinality at most |K|, hence exactly |K| by minimality. C1 then gives an ORIGINAL optimum using only representative source edges. Edges with empty incidence occur in no minimum transversal unless H is empty, in which case the empty cutset is optimal.

Column inclusion gives a polynomial reduction preserving at least one original optimum. Pairwise comparisons of O(n) edge columns against O(n^4) conflicts take O(n^6) time in a simple explicit representation. The equal-halves witness illustrates the rule: the edge separating {c,d} is dominated; the maximal class consists of the three singleton edges b,c,d and can be represented by b. The crossed quartet still has five maximal incidence classes despite optimum two. Enumerating representative cutsets has worst-case size sum_{i<=b} binom(M,i), where M is the number of maximal incidence classes. Bounding this enumeration by (5/4)^b or (3/2)^b remains open.

## Precise remaining theorem

### C6: a one-output safe separator family

Let Q be a rooted binary tree on m>=2 distinct indices. Let Q_A and Q_B rename index i to a_i and b_i, respectively. Set S=(Q_A,Q_B). Replace every indexed leaf i of Q by cherry (a_i,b_i) to obtain T. Then the original optimum is exactly m. The source root-edge cut into the sectors A and B preserves an optimum, and both components agree with their target restrictions. The output is all-compatible, has one nonredundant precut and tau=0, and completes with m-1 additional cuts. Constructing this single output takes polynomial time; it satisfies the safe-cover properties for this family when b>=m.

For the lower bound, consider an arbitrary agreement partition. If a target cherry's two labels a_i,b_i lie in one block, they form a cherry in that block's target restriction. Their source LCA is the root of S; any third label in that block would lie with a_i or b_i below one source child, preventing a_i,b_i from being a source cherry. Hence such a block must be the pair {a_i,b_i}. At most one of these paired blocks is possible, because all their source paths contain the source root.

Realize the agreement partition by q=|P|-1 nonredundant target cuts, using the normalization argument above. Every split target cherry requires one of its two pendant edges to be cut, and those edges are distinct across cherries. If all m cherries split, q>=m. Otherwise exactly one pair is retained and m-1 cherries split. Suppose q<=m-1. The target cuts then consist of exactly one pendant edge at each split cherry and no other edge. The remaining target component contains the retained pair and one label from each other cherry. Since m>=2 it contains a third label, contradicting the retained-pair block characterization. Thus q>=m in all cases.

For the upper bound, use all m A-label singletons and the whole B-sector. Their source and target embeddings are vertex-disjoint, and the B restrictions are both Q_B. This gives m+1 agreement pieces and m cuts. The same partition refines the root-sector precut: realize it by one root-edge cut and m-1 additional cuts isolating all but one A label inside Q_A. Every cut creates two nonempty label parts. The charged total is m, proving safety without assuming that arbitrary root separators are safe.

The m>=2 hypothesis is sharp. At m=1, S=T=(a_1,b_1) has optimum zero, and the source sector cut excludes that optimum. The finite controls detect this exception. C6 is a handwritten source-model proof, pending fresh nonauthor review; it proves a structured family rather than the unrestricted generation theorem.

### General sparse enumeration

Construct, from the conflict family and source/target geometry in paid O*(alpha^b) time, at most O*(alpha^b) partial ORIGINAL source cutsets C_j, such that each induced forest is terminal, at most b cuts are made, every pure output has certified ORIGINAL unmarked local distance at most b/2, and at least one C_j is a subset of some minimum H-transversal (or directly has an optimum agreement partition refining it). The local-distance certificates cannot be obtained by an uncharged optimizer. Column domination and conflict packing are allowed polynomial preprocessing/certificates; neither supplies this enumeration theorem. Alpha=5/4 exact target; alpha=3/2 licensed alternative only with paid completion and interface proofs.

Pure-bridge G1-G7, triple G1-G3, marked-query role swap, source executable correspondence, reduction history, and original-label reconstruction remain conditional imports. The arithmetic consumer cannot close those interfaces.
