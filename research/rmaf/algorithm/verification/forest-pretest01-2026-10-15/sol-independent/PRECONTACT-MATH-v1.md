# Independent mathematical route before candidate source contact

Written after READY freeze while awaiting exact release. These are reviewer
inferences from the licensed definitions, not extracted candidate claims or
a formal proof. Incidental summary exposure remains qualified in READY.

For proper input each current source component has a nonempty, disjoint
label set. Every actual full-state AF refines those sets. Its blocks can
therefore be grouped uniquely by current source component, and each group
has at least one block. In particular |F| >= |ss|; Nat subtraction is
ordinary subtraction on such AFs. Additional cost is the sum over source
components of (number of final blocks in that component minus one).

If that cost is zero, each current source contributes its whole label set.
If the cost is one, exactly one current source contributes two complementary
nonempty label blocks and every other component remains unchanged. The two
original source hulls are vertex-disjoint connected subgraphs. The unique
path connecting them has an original edge between the two hulls; deleting
such an edge separates the two label classes. To justify the last sentence,
if either class had selected leaves on both sides of that edge, its connected
hull would contain the edge, contradicting its position between the disjoint
hulls. Since the two classes exhaust the source leaves, the two graph
components have exactly the desired label sets. The edge is a genuine
nonroot edge of that current source tree, and enumeration need only retain
the other current source blocks. No global original-source cut union is used.

Thus the mathematical coverage route uses a separation edge between the
two actual source hulls, without target partition disjointness assumptions.
The target full-state predicate must still be checked on the entire
candidate; internal target overlap across current source components is not
excluded by properness. Permuting inner labels and outer blocks preserves
the full predicate. Coverage then permits global minimum and rejected-cost
conclusions: a found cost-one answer excludes actual cost-zero only after
candidate coverage and best's true minimum property; rejection excludes
every actual cost-at-most-one AF. A cost-zero answer is trivially globally
minimum because Nat costs are nonnegative. None of these statements follows
from candidate-list minimum alone.

The empty state is distinct: proper (None,[]) has only empty final partition
and cost zero; a nonempty target with no source components fails properness.
Refusal is a malformed-input result, not an infeasibility certificate.

For a nonempty binary current tree with n_i leaves, original vertices number
2 n_i - 1 and edges number 2 n_i - 2. For r current components and n total
leaves, the generated list has 1 + 2n - 2r entries, including repeated
partitions. For empty input it has one entry. Both give the qualified upper
bound 1 + 2n. This counts candidates, not instructions: original address
lengths, repeated subtree leaf scans, restriction/topology checks, original
hull calculations, pairwise list membership and returned payload must be
audited separately. Arbitrary Nat-label bit costs cannot be replaced by
constant-time label arithmetic.

Postrelease checks must establish that the actual quantified formal
statements, permutation relation, properness, separation lemma and use sites
really implement this route without a desired-coverage hypothesis or
exponential callback. Global milestones remain OPEN.
