# Source-level polynomial construction audit

Scope: building grouped literal states and concatenating their supplied block
families. This is a mathematical audit of the source programs, not a formal
compiled-machine cost semantics and not the full algorithm runtime milestone.
No helper-call counter is identified with individual machine instructions.

Let N bound the total number of tree nodes, list cells of labels, source trees,
groups, and supplied forest blocks at the call boundary; let b bound the bit
length of every Nat label. On valid checked partitions, label occurrences and
block/source/group counts are also bounded by N. Lists are represented
literally, and unary paths are preserved by minimalVertices even when tree
restriction suppresses them.

* `leaves` in RMAF traverses each subtree and appends child lists. Charging each
  label once per ancestor gives O(N^2) cells traversed and allocated. Nat equality
  and membership have O(b+1) per comparison and O(N(b+1)) per list scan.
* `restrict U t` traverses every original node and checks selected membership
  at each leaf. Suppression returns the surviving child directly. A call costs
  O(N^2(b+1)); constructing every local target in Q costs O(N^3(b+1)).
* `owned ss U` filters the existing tree references; it never cuts or rebuilds
  a source tree. Recomputing leaves pessimistically and checking every
  containment costs O(N^3(b+1)) for one group and O(N^4(b+1)) for all groups.
* `family U F` scans existing blocks and compares each label with U. Even with
  repeated scans, building every local family costs O(N^3(b+1)). Concatenation
  uses List.flatMap and list append on supplied block references. Charging
  every block once per group gives O(N^2) list cells. AdditionalCost reads the
  list lengths and subtracts natural numbers; summing over Q is polynomial.

Thus the literal constructions used by the two reconstruction directions have
the conservative source-level bound O(N^4(b+1)), excluding calls to any future
solver. The proofs about these constructors are erased and add no executable
search. No number of proof declarations is a runtime measure.

For completeness, checking the graph input and supplied agreement witnesses is
also polynomial under these literal definitions. `rootedSpan` prepends one Bool
to vertex addresses on each ancestor traversal. A vertex address has length at
most N. Charging repeated address creation pessimistically gives O(N^3(b+1))
for one `minimalVertices` call, including its repeated rootedSpan calls.
`disjointVertices` scans at most N vertex addresses against at most N others,
with O(N) Bool-address comparisons, so it costs O(N^3). At most O(N^2) source
pairs are needed for CrossClear; no within-group pairs are needed there.
`sameShape` visits at most one instance of each pair of equally deep subtree
roots, hence at most O(N^2) pairs. Each pair has one fixed parent pair, so no
recursive pair has two routes from the original root pair. It performs a
constant number of recursive child-pair calls and label comparisons per pair.
Partition, refinement, restriction-agreement, and embedding checks can all be
bounded conservatively by O(N^7(b+1)) for the entire finite call boundary,
including repeated source checks and recomputations. The loose exponent allows
all naive list scans; no caching or bitset implementation is assumed.

The universal proof does not run an enumeration over assignments, edge sets,
or all possible local agreements. `ResidualSolverContract` names an assumed
child solver result and supplies no complexity bound for obtaining it. The
finite controls use kernel decide on fixed small trees; their timings measure
those replay invocations only. They do not establish an asymptotic runtime.

Source locations: GroupDefs.lean lines 9-17 (constructors and graph predicate),
GroupForwardProof.lean lines 22-56 (forward use), GroupReverseProof.lean lines
76-137 (reverse use), GroupCostProof.lean lines 53-95 (cost), RMAF.lean
`leaves`, `restrict`, `sameShape`, `rootedSpan`, `minimalVertices`,
`disjointVertices`, and `partitionCheck` (primitive list programs). An
independent formal fine-step cost proof is not supplied.
