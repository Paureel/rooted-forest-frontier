# Exact transfer from unaugmented rooted MAF

Status: **Provisional mathematical proof**. The two-marker construction gives an exact component-count transfer for ordinary agreement forests of nonempty, uniquely labelled rooted binary trees, using a unary labelled rho root. Lean checks 11 supporting declarations in a binary sister-leaf rho model; the full forest maps and the equivalence of rho encodings remain unformalized. The runtime consequence assumes correctness and the reported cost bound of the thesis algorithm. No new algorithm or global novelty claim is certified here.

A fresh scope reviewer found no mathematical gap in the argument below. That bounded review did not include a new exact enumerator or the protocol’s forced-diversity proof review, so the provisional status remains.

## Definitions and scope

Let T1,T2 be nonempty rooted binary phylogenetic trees with the same leaf set X, with labels used once per input. An ordinary agreement forest is a partition P of X into nonempty sets, with isomorphic rooted restrictions for each block and pairwise vertex-disjoint minimal spanning subtrees in each input. Write K(T1,T2) for its minimum component count. There is no acyclicity condition.

A thesis augmentation adds a fresh vertex labelled rho above the original root, with that root as its sole child. The rho label belongs to the label set. For a block containing rho, the minimal span includes the path from rho to its other labels, and the labelled rho vertex is retained during suppression. Write Krho for augmented minimum component count. Whidden's Chapter 2 printed p12 defines this convention; printed p15 relates rooted SPR distance to Krho−1. These conventions are retrieved, not newly introduced here.

Two elementary facts used below:

1. Restricting an agreement partition to a subset of its labels and dropping empty blocks gives an agreement partition of the restricted input trees. For each surviving block, its new minimal span is contained in its former minimal span, so disjointness survives. Restriction is transitive after suppressing unlabeled vertices of outdegree one, so the two new rooted restrictions remain isomorphic. This fact does not split a single old block into two components.
2. Every path from a vertex outside a descendant subtree T to a vertex of T passes through the root of T. This is uniqueness of paths in a tree.

## Direct augmentation is not an equality reduction

For every pair, K ≤ Krho ≤ K+1. Delete rho for the lower bound, using Fact1. For the upper bound, add the singleton block {rho}; all old spans lie strictly below rho. The optimum with rho forced to be singleton equals K+1 exactly, by the same maps in both directions.

The bounds can differ: T1=(a,(b,(c,d))) and T2=(c,(d,(a,b))) have K=2, witnessed by {a,b}|{c,d}, and Krho=3. In each tree the two blocks' ancestor order is opposite. Rho cannot join either block without its span meeting the other block in one input. No 3+1 partition agrees because all four rooted triple restrictions disagree; the other 2+2 partitions overlap. The finite oracle independently reproduced these exact values. The two-block witness has a directed ancestor cycle and is permitted under the ordinary-AF definition.

## Exact two-leaf construction

Choose distinct fresh leaves alpha,beta, neither in X. Construct rooted binary trees

    U1 = (beta, (alpha, T1)),
    U2 = (alpha, (beta, T2)),

and then augment each with the thesis's unary labelled rho root. Call the augmented trees A1,A2. The new ordinary leaf count is |X|+2; the augmented label set is X ∪ {alpha,beta,rho}.

**Theorem.** Krho(U1,U2) = K(T1,T2)+1. Moreover, deleting alpha,beta,rho from the blocks of any minimum AF of A1,A2, and discarding empty blocks, produces a minimum ordinary AF of T1,T2.

**Upper bound and explicit map.** Let P be any ordinary AF of T1,T2. Add the single block S={alpha,beta,rho}. Its rooted restrictions agree: both are the unary labelled rho above a cherry with leaves alpha,beta. Its span consists only of the new root-path vertices and the two new leaves. It excludes the root and every other vertex of the original T_i subtree. Thus it is vertex-disjoint from every old block span. Old block restrictions and spans are unchanged inside T_i. Therefore P∪{S} is an augmented AF with |P|+1 blocks. In particular Krho≤K+1.

**Lower bound and explicit map.** Let Q be any augmented AF of A1,A2. Call a block mixed if it contains both a label in X and at least one of alpha,beta,rho. In either input, the span of every mixed block includes the root of the original T_i subtree by Fact2. Vertex-disjointness therefore permits at most one mixed block.

A mixed block cannot contain both alpha and beta. If it also contains x∈X, restrict that block further to {alpha,beta,x}. In U1 the cherry is alpha,x, with beta above it; in U2 the cherry is beta,x, with alpha above it. The rooted labelled triples differ, contradicting the block's agreement by Fact1. The same argument applies if the block also contains rho; restricting to the three stated leaves deletes rho.

There must consequently be a block of Q with no X label. Otherwise both blocks containing alpha and beta would be mixed; they cannot be different (at most one mixed block), and cannot be the same (incompatible triple). Delete the three new labels from every block and drop empty blocks. Fact1 gives an ordinary AF P of T1,T2; at least the identified pure-new block is dropped, so |P|≤|Q|−1. Hence K≤|Q|−1, proving Krho≥K+1.

For a minimum Q, |P|≤Krho−1=K, while optimality of K gives |P|≥K. Therefore |P|=K. This also shows that exactly one block is dropped when Q is minimum. The maps use no acyclicity premise.

## Runtime and output interface

Let n=|X|. Conditionally on a correct implementation of the thesis's augmented rooted-SPR/MAF algorithm and its reported bound, this construction gives an exact ordinary rooted-MAF algorithm with O(2^K (n+2)) decision time: the target augmented cut parameter is q=Krho−1=K. Thus the no-rho convention does not by itself block transfer of the claimed result with exponential base 2.

Iterating q from zero until the first affirmative answer gives the optimum with the same geometric-order time bound. At the first affirmative threshold, if the successful recursive branch exposes its cut forest within the stated time bound, retaining that forest gives a minimum augmented witness; erasing the three new labels gives a minimum ordinary AF. The witness-retention implementation has not been reconstructed in this campaign.

The runtime consequence remains **conditional on the thesis algorithm's correctness and cost proof**, which have not been fully reconstructed or formalized. The algorithm and its claimed bound are retrieved prior work; the convention-transfer proof is provisional.

## Lean interface trace

Transfer.lean imports the campaign's RMAF definitions only after the independent Python controls passed. It uses the binary sister-leaf encoding of rho (`augment rho t = node (leaf rho) t`), while the Python oracle uses the thesis unary labelled-root encoding. Replace the labelled unary root by an unlabeled root whose children are a new rho leaf and the former child. The rho singleton remains a singleton, and every nonsingleton rho block uses exactly the same vertices of the unaugmented tree. A crossing with an old-only block therefore occurs at the same vertex in either encoding, and restriction isomorphisms correspond under this replacement. This equivalence is argued here but **not formalized**.

The 11 audited declarations cover:

- direct disagreement of a block containing both markers and nonempty old restrictions;
- nonempty rooted spans and retained root vertices;
- actual inclusion of the old subtree root in each mixed block's minimal vertex list;
- non-disjointness of two mixed blocks at that common vertex;
- optimum shift given explicitly supplied upper/lower AF maps;
- q=K arithmetic once the shift is known.

The conditional optimum theorem has old/new minima and both semantic maps as explicit hypotheses. It does not discharge them. Still needed for an unconditional full Lean transfer theorem: finite-partition add/erase validity and counts; hereditary restriction/disjointness; bridge between unary-root and sister-leaf rho models. The thesis protected-edge solver is not imported or verified by these lemmas. Python and Lean share the stated mathematical definition but no implementation; their algorithms/representations differ. Neither is called a fresh independent certification of the other's universal theorem.
