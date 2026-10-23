# Exact elimination and polynomial completion for rooted agreement forests

Research note developed in this conversation, 9 October 2026.

## Status and scope

This note gives two handwritten structural theorem arguments, executable algorithms, and finite checks. It does **not** establish a new unrestricted exponential base for rooted Maximum Agreement Forest (rMAF). The new claims have not been independently refereed or machine-checked, and priority has not been established. They do not assume the earlier proposed 2.3203 or 2.2775 algorithms are correct.

The two results concern the **completion problem** encountered inside an exact solver: given a target rooted binary tree T and an already-cut source forest F, find a minimum agreement-forest refinement of F. A refinement cannot merge leaves from different source components. Cutting the original source tree arbitrarily to enter one of these classes is NOT a safe reduction of the original problem.

Result A eliminates all interaction choices in a pure-bridge instance with any number of components, including an arbitrarily large complete overlap graph. With d_i the ordinary local cut distance of component i from its target restriction, it runs in O*(c^max_i d_i), using a rooted tree--forest solver of base c. The supplied complete implementation uses the classical base c=1+sqrt(2); substituting the verified published 2.3391 solver gives the corresponding theoretical bound.

Result B solves completion in polynomial time whenever every incompatible source component has three leaves, with arbitrary compatible components and arbitrary overlaps. Its value dynamic program has O(nm) states and transitions for n leaves and m source components.

## 1. Definitions

A rooted binary tree is represented mathematically as an unordered rooted binary tree with distinct labeled leaves. Let T[B] be the unsuppressed minimal subtree spanning a nonempty leaf set B, and T|B its rooted restriction. Roots inherit the orientation of T; suppress indegree-one/outdegree-one vertices.

For a source component D, write L_D for its labels and S_D=T[L_D] for its target embedding. A local agreement forest of D is a partition P of L_D such that:

1. D|B=T|B for every B in P;
2. the embeddings of distinct blocks are vertex-disjoint in D and in T.

A global refinement chooses such partitions for all source components and additionally requires all their target embeddings to be pairwise vertex-disjoint. Its additional cut count is |P|-|F|. No acyclicity condition is imposed. No root label rho is silently added by the code. It can be supplied as an ordinary input label when that convention is intended.

The minimum additional-cut count for D alone is d_D. For a set J of unlabeled target vertices, define

    h_D(J) = min { |P|-1 : P is a local agreement forest of D,
                         T[B] avoids J for every B in P }.

Only marks of degree two in S_D are needed in the elimination theorem. The code can solve other feasible marked queries as well, but the one-cut exchange proof is not asserted at degree-three vertices.

## 2. Pure-bridge geometry

Call an overlap between A and B **pure** if every vertex v in S_A intersect S_B has degree exactly two in S_A and exactly two in S_B. Assume in this section that every overlap between different source components is pure.

### Lemma 2.1 (whole-overlap clearance)

If A and B overlap purely, Q=S_A intersect S_B is a path, and the leaves of each component occupy exactly two exterior sectors off Q. A block of A whose embedding uses one vertex v of Q uses all of Q. A block of A avoiding v avoids the entire embedding S_B. The symmetric statements hold for B.

**Proof.** Intersections of subtrees of a tree are connected. Q has maximum degree two in both embeddings, hence is a path. It contains no leaf of either source component, since the label sets are disjoint and a target leaf cannot be an internal vertex of an embedding for another label set. At an interior vertex of Q there is no unused incident edge in either embedding along which that component could branch. At an endpoint of Q each embedding has exactly one exit edge, and their exit edges differ; otherwise Q would extend farther. All leaves of each component therefore lie beyond its two exits. A block meeting both sectors uses every vertex of Q; one contained in a sector has its embedding outside Q. Its embedding is a subset of S_A, so avoiding Q also avoids S_B. Q cannot consist of a single vertex in a subcubic target: two degree-two subtrees at that vertex would share an incident edge. This also accounts for a target root of degree two. QED.

### Lemma 2.2 (marked one-cut inequality)

For a degree-two vertex v of S_D,

    h_D(J) <= h_D(J union {v}) <= h_D(J)+1.

**Proof.** The first inequality follows by imposing an additional constraint. Take an optimum for J. At most one of its pieces uses v. If no piece does, there is no added cost. Otherwise, because v is unlabeled and has degree two in S_D, that piece has labels on both sides of v. Split it by the bipartition induced by v. In its agreeing source restriction this is an edge split (including a child-edge split if v is the root of the restriction). The new pieces remain agreement pieces, are vertex-disjoint, avoid v, and still avoid all old marks. Exactly one extra nonempty piece is added. QED.

### Lemma 2.3 (deepest-root neighborhood)

Among remaining components choose A whose embedding root v has greatest depth in T. Every remaining component B overlapping A contains v.

**Proof.** Choose z in S_A intersect S_B. The roots of S_A and S_B are ancestors of z and therefore comparable. By the depth choice, the root of S_B is an ancestor of v. The path from that root to z passes through v and belongs to S_B. QED.

In particular, the neighbors of A form a clique through v; their number is unbounded. If A has a neighbor, v has degree two in every one of these embeddings by purity.

## 3. Elimination algorithm and proof

Maintain marks J_D for every remaining component. Initially they are empty. Repeatedly choose a deepest-root component A, with root v, and compute mu=h_A(J_A).

- If A has no remaining neighbors, fix a mu-cost witness and delete A.
- Otherwise test whether h_A(J_A union {v})=mu.
  - If yes, fix a mu-cost witness avoiding v and delete A.
  - If no, fix a mu-cost witness for J_A, add v to J_B for every remaining neighbor B, and delete A.

The bounded test in the second step is made at cost mu, not by unboundedly recomputing a harder optimization problem. By Lemma 2.2 failure means the marked optimum is exactly mu+1. A test whose mark is already present is skipped.

### Theorem A (exact global pure-bridge elimination)

This algorithm returns an optimum global agreement-forest refinement. It makes at most two local optimization queries per original component and does not branch on interaction choices.

**Proof.** We prove preservation of the optimum at each elimination, accounting for an additive mu.

With no neighbors, independence is immediate. When the marked and ordinary optima are equal, the chosen marked A-witness avoids every neighbor by Lemma 2.1, since every neighbor contains v. It can replace the A-part of any global solution without increasing cost or creating an overlap. Thus the optimum is mu plus the optimum of the unchanged remaining marked problem.

Suppose instead the penalty for forbidding v is one. Any mu-cost A-witness uses v. Requiring every neighbor to avoid v therefore makes its union with that witness feasible, including full path clearance by Lemma 2.1. This gives one direction of the optimum equality.

For the other direction, start with any optimum global marked solution. If its A-pieces use v, all other pieces already avoid v, and A can be replaced with the chosen mu-cost witness. If its A-pieces avoid v, their cost is at least mu+1. Among ALL other pieces, at most one uses v because global pieces are vertex-disjoint. If one does, it belongs to a neighbor B and can be split at v at cost at most one by the construction of Lemma 2.2. This preserves all its existing marks and makes all remaining pieces avoid v. Replacing the A-pieces with the chosen mu-witness saves at least one cut and pays for that possible split. The new global solution costs no more and satisfies the imposed neighbor marks.

Consequently, the original optimum equals mu plus the optimum of the newly marked remaining problem. Induction proves the theorem and the correctness of the union of recorded witnesses. There is no assumption that unqueried mark penalties add independently. QED.

This proof permits a complete overlap graph of arbitrary size. It does not rely on there being two or three components, nor on any component being compatible.

## 4. Paying for all local queries: a parameter-preserving role swap

Theorem A would be misleading if its marked queries were treated as free. The following reduction gives an explicit cost bound.

Delete the marked vertices J from S_D and let C_1,...,C_r be its nonempty leaf regions. Ignore empty regions. Construct the forest

    G_J = { T|C_1, ..., T|C_r }.

Then a marked local agreement forest of D is exactly a common agreement-forest refinement of the **target tree D and source forest G_J**. Roles have been swapped: G_J is already cut into r components.

### Lemma 4.1 (exact parameter reduction)

The additional-cut optimum for (D,G_J) is

    q_J = h_D(J) - (r-1),

and satisfies

    0 <= q_J <= d_D.

**Proof.** Both problems have precisely the same allowable final leaf partitions. A solution with h_D(J)+1 pieces requires h_D(J)+1-r additional cuts in the already-r-component source forest G_J, establishing the identity and nonnegativity.

The region partition is a convex partition of the target restriction: it can be obtained with r-1 nonredundant target-edge cuts. To justify the count even when deleted marked vertices leave empty intermediate regions, extend each nonempty region across unassigned vertices until the whole tree is partitioned into r connected parts; then cut their r-1 boundary edges. The induced leaf partition is unchanged.

Take an ordinary d_D-cut local agreement forest. Enforce those r-1 target-edge partitions one at a time. At each edge, at most one current agreement piece crosses it; split that agreeing piece at the corresponding source edge. At most r-1 new pieces are added. Thus h_D(J) <= d_D+r-1, proving q_J <= d_D. QED.

For the comparison query J union {v}, the new number r' of leaf regions is at least r. Its allowed additional-cut budget is

    mu-(r'-1) <= mu-(r-1) <= d_D.

If this bound is negative, the test fails immediately. Iterative deepening for the first query and a bounded optimization for the second therefore never need residual cut budget greater than d_D. There are at most 2m queries, and all instances have at most the original number of labels.

### Corollary 4.2 (exponent depends on the hardest component)

If a rooted tree--forest optimizer runs in O*(c^q), pure-bridge completion runs in

    O*(c^tau),       tau = max_D d_D.

Polynomial factors absorb the number of components, geometry preprocessing, and all calls. This is NOT a bound in terms of an unaccounted oracle, and tau is defined for the original unmarked components, not adaptively enlarged marked problems.

The supplied `marked_fpt.py` uses `basic_fpt.py`, an explicit reference implementation of the classical rooted cherry rules. Those rules have recurrence bounded by

    2 R(q-1) + R(q-2),

with the one-pendant case forced and different-component cherries giving 2 R(q-1). Thus the implemented bound is

    O*((1+sqrt(2))^tau).

This classical base is credited, not claimed as new. Replacing this reference optimizer with the published split-or-decompose tree--forest optimizer yields O*(2.3391^tau) in the same proof. The latter solver has not been reimplemented in this bundle.

When every local d_D is bounded by a constant, this algorithm is polynomial even if the optimum total completion cost and the overlap graph are arbitrarily large. When F has only one component, tau is exactly the original rMAF cut parameter, so this result alone gives no improved unrestricted base.

## 5. An explicit family demonstrating the distinction

For each i=1,...,m use a private incompatible rooted triple

    U_i = ((a_i,b_i),c_i),   U'_i = ((a_i,c_i),b_i),

and a private common rooted tree R_i with five leaves. Set D_i=(U'_i,R_i). Construct T with a root whose left child contains all U_i on a binary backbone and whose right child contains all R_i on another binary backbone.

The source forest has m components, each with eight leaves and local distance one. Every pair of embeddings overlaps purely: their intersection is the unbranched path across the shared central split, and they branch only after their private routes separate. The overlap graph is K_m.

Every component needs one cut to fix its triple. At most one final piece can cross the central target edge. For all but at most one source component, avoiding that edge requires an additional sector-separating cut beyond the triple cut. A one-cut forest that fixes the private triple retains a piece with some left labels and right labels; a one-cut forest separating the sectors leaves the incompatible triple intact. Hence any solution needs at least

    1 + 2(m-1) = 2m-1

additional cuts. Isolating one triple leaf in every component, and separating the two sectors in all but one component, attains this bound.

The implementation solves the m=60 instance with n=480, optimum 119 additional cuts, 61 local queries, 181 recursive calls of the local FPT solver, and maximum successful residual oracle budget one. These counts are reproducible; recorded wall-clock timings are environment-specific, not comparative speedup claims. This is a completion instance, not a claim that arbitrary two-tree instances with distance 119 have been solved in constant time.

## 6. Polynomial completion with incompatible triples

Now discard the pure-overlap assumption entirely. Suppose every source component either agrees with its target restriction, or has exactly three leaves.

Color each target leaf by its source component. Call a color good when the component agrees, and bad when its three-leaf source topology differs.

### Lemma 6.1 (exact characterization)

A partition is a valid refinement exactly when its target embeddings are vertex-disjoint, every block is monochromatic, and no block contains all three leaves of a bad color.

**Proof.** For a good color, the whole source component and its target restriction are isomorphic. Therefore any target-convex partition of its labels transfers to vertex-disjoint matching source pieces. For a bad three-leaf color, every proper partition consists of a pair and a singleton, or three singletons. The pair topology is unique, and the singleton leaf lies outside the pair's minimal span in both source and target. Thus every proper partition is locally valid, whereas the unsplit triple is invalid. Different source colors occur in different source components and impose no additional source-overlap condition. QED.

### Dynamic program

At each target vertex v, at most one connected region can use v and remain open toward its parent. Maintain these states:

- None: no open region uses v;
- (i,0): one open region has good color i;
- (i,S): one open region has bad color i and contains the nonempty subset S of its three leaves, with |S|<=2.

Store the minimum number of closed nonempty regions below v. An open region is not yet charged. There is one state per good color and at most six per bad color. A leaf initializes its own open singleton state at cost zero.

For child w let

    C_w = min( DP_w(None), 1 + min_{s active} DP_w(s) ).

This is the cost of closing everything in that child. For an internal vertex with children l,r, consider:

1. Leave v unused: state None at cost C_l+C_r.
2. Extend just a left open region: DP_l(s)+C_r.
3. Extend just a right open region: C_l+DP_r(s).
4. Join two open regions of the same color: DP_l(s)+DP_r(t), with the union of bad-color masks having size at most two.

For equal resulting states keep the minimum. At the root take the smaller of a None value and an active value plus one. Subtract m from the resulting minimum number of regions to obtain additional cuts.

### Theorem B (polynomial terminal class)

This dynamic program is exact and its value computation takes O(nm) time and space, in addition to polynomial input validation. A backpointer implementation reconstructs an optimum forest in polynomial time.

**Proof.** In any collection of disjoint connected regions, at most one region meets v. It either joins two child regions of the same color, extends one, or has no leaf below v and can be trimmed away without harm. Regions not extended toward v close inside their child. These possibilities are exactly the transitions above. Bad masks enforce precisely the only additional forbidden partition from Lemma 6.1. No information about closed good-color regions is needed: target disjointness implies source disjointness under their fixed isomorphism. No information about closed bad-color regions beyond the open mask is needed: any proper partition of three leaves is valid. Induction on the target tree proves the DP invariant and optimality.

Each color contributes a constant number of states and candidate joins at each vertex: at most 36 ordered pairs for a bad color. Closing minima and one-child extensions are linear in the state count. Thus time and space for values and backpointers are O(nm). The supplied simple witness constructor copies label sets and may take O(n^2) extra time; this remains polynomial and is not concealed in an O(nm) implementation claim. QED.

Two adjacent regions may have the SAME color and still have to remain separate. Consequently this is not ordinary Fitch parsimony on the input colors: for the one-color input T=((a,b),c), D=((a,c),b), ordinary parsimony makes zero changes, but the correct completion requires one cut.

The all-compatible subcase is already a known Fitch/parsimony reduction used in the published 2026 algorithm. It is not a discovery claimed by this note.

## 7. Precise obstacles to a general compression argument

### 7.1 Mark costs are neither submodular nor supermodular

Take T=((a,b),c), D=((a,c),b). For J subset {a,b,c}, now let h(J) denote the optimum when each leaf in J must be a singleton. These are edge-separation constraints; do NOT model them by forbidding the leaf vertex, which would be infeasible.

Then h(J)=1 when |J|<=1, and h(J)=2 when |J|>=2. Hence

    h({a})+h({b}) < h(empty)+h({a,b}),
    h({a,b})+h({b,c}) > h({b})+h({a,b,c}).

Single extra penalties all vanish, but two imposed constraints can have positive joint penalty. Independent one-bit penalties are not a valid unrestricted compression.

### 7.2 Explicit representative lists can need 3^r witnesses

Attach r private incompatible triples of the preceding shapes to a common rooted binary backbone and include a shared anchor leaf rho. The ordinary optimum is r cuts. Every optimum must cut inside each private triple, so with r cuts it makes exactly one such cut in each and no backbone cut.

The three possible singleton cuts in each triple work. Cutting off the source cherry instead does not: its target span shares the triple root with the component containing the remaining triple leaf and rho. Cutting off the whole triple leaves its topology incompatible. Thus there are exactly 3^r optimum partitions, indexed by the choice of singleton in each triple.

For each vector of singleton choices, require those r leaves to be singletons. Exactly one optimum partition satisfies that context. Therefore an explicit list of optimum witness forests that must answer every context by selecting a stored witness needs at least 3^r entries.

This is a representation-specific lower bound, NOT a lower bound on all algorithms or compact factorizations. The independent gadgets themselves have a compact product representation. The elimination theorem avoids this obstacle by making only the adaptively selected queries justified by the overlap geometry, rather than storing answers for every context.

### 7.3 A cut-only branching analysis cannot beat two while keeping two unit branches

If a recurrence retains two uncredited one-cut recursive calls, its frontier weight has form 2/c+R(c) with R(c)>=0. Weight at most one requires c>=2. Any proof of a sub-two algorithm must therefore change state sharing, amortization, reductions, or the branching architecture itself. This is not a complexity lower bound for rMAF.

## 8. A concrete sufficient missing lemma for an unrestricted improvement

The following is a research target, NOT a theorem claimed here.

**Balanced safe-cover target.** Given a reduced rooted tree pair and cut budget b, construct in O*(1.25^b) time at most O*(1.25^b) source-forest refinements F_j, with all of the following properties:

1. Every F_j is obtained using at most b counted, nonredundant source cuts.
2. If the original pair has optimum at most b cuts, at least one original optimum refines some F_j.
3. Every F_j is a pure-bridge completion instance, or belongs to the polynomial triple class.
4. For every pure-bridge F_j, the maximum ordinary local cut distance is at most b/2.

Given this lemma, complete each F_j exactly, add its already-made cuts, and take the minimum. The implemented local base would give

    O*((1.25 * sqrt(1+sqrt(2)))^b)
      = O*(1.9422174676^b).

Using the published 2.3391 local base instead would give O*(1.9117645645^b). No oracle difficulty or pre-cut cost is omitted from this conditional implication. But the safe-cover construction and its size bound have NOT been proved. Choosing an arbitrary approximation forest is not enough: it can exclude every optimum. The numerical implication is easy; the missing structural coverage is substantial.

## 9. Verification and its limits

The bundle's verification programs are deterministic and use fixed random seeds for sampled tests. They compare optimum values and reconstructed witnesses, rather than only branching roots.

- Known all-compatible baseline: 5,460 exhaustive five-leaf tree/partition inputs.
- Pure-bridge elimination using complete partition oracles: 3,069 completion inputs; 10,054 eliminated components, including 367 instances with an overlap triangle and 282 high-degree elimination steps.
- Triple DP: 9,660 exhaustive five-leaf forest inputs, 8,505 six-leaf two-triple inputs, and 600 sampled seven-to-ten-leaf inputs, totaling 18,765 optimum comparisons.
- Marked role-swap identity: 300 sampled cases.
- Profile representative obstruction: all choices through four gadgets, with 3,9,27,81 optima and matching uniquely forcing contexts.
- Classical FPT implementation: 32,970 budget checks covering all 105^2 rooted five-leaf tree pairs, plus 1,428 sampled tree--forest budget checks.
- Full marked-FPT/elimination integration: 362 further pure-bridge completion comparisons.
- Large triple-DP witness-only test: 600 leaves and 200 source components, including 134 incompatible triples. Its witness is checked, but this large case is not independently exhaustively optimized.
- Large pure-bridge family: 480 leaves, 60 eight-leaf incompatible source components, complete overlap graph, independently proved optimum 119 additional cuts.

Tests share some tree primitives; they are not independent formal verification. Exhaustive statements above refer only to the enumerated sizes and specified source families. Nothing in this bundle is a Lean certificate. No general rMAF speed record is inferred from the restricted large examples.

## 10. Prior art and references

1. David Mestel, Steven Chaplick, Steven Kelk, Ruben Meuwese. *Split-or-decompose: Improved FPT branching algorithms for maximum agreement forests*. JCSS 160, 103800 (2026). Rooted bound 2.3391; Section 4's tree--forest optimization interface; Branching rule 7 and Lemma 15 for the all-compatible Fitch reduction.
   - https://arxiv.org/html/2409.18634v2
   - https://cris.maastrichtuniversity.nl/en/publications/split-or-decompose-improved-fpt-branching-algorithms-for-maximum--2/

2. Chris Whidden. *Efficient Computation and Application of Maximum Agreement Forests*. PhD thesis, Dalhousie University, July 2013. Chapter 6 states a base-two theorem and includes an algorithm and correctness/running-time proofs; this is more than a software README claim. Theorem 6.1 is on printed page 100, Theorem 6.12 gives correctness, and Theorem 6.13 begins on printed page 116 and concludes on printed page 126. Chapter 3 contains the older (1+sqrt(2)) algorithm used as the reference local solver here.
   - https://dalspace.library.dal.ca/bitstreams/3b246ff4-5ec2-452f-95ab-ef1aed255373/download
   - https://hdl.handle.net/10222/35349

   This turn recovered the thesis's parsed full text. PDF screenshot retrieval failed, and the complete graphical case analysis has not been independently verified. Its root/SPR convention must be distinguished from bare MAF without rho. The 2026 paper explicitly notes that the thesis advancement remains unpublished. These facts do not justify dismissing the thesis theorem or claiming priority over it.

3. Author-maintained rSPR repository, which also describes the base-two claim:
   - https://github.com/cwhidden/rspr

The two structural results in this note have not been found in the searches performed, but a negative search does not establish novelty. They should be circulated as proposed structural results with explicit proofs and code, not as a certified new fastest unrestricted rMAF algorithm.
