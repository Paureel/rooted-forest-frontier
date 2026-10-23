# Source-level polynomial runtime argument

Let `N = treeSize T + treeSize S`, let `b` bound the bit length of any original
label, and charge constant time per Boolean operation and list constructor,
`O(b)` per original-label equality, and linear time in address length per
original-address equality. This is a bound on ordinary execution of
`Pretest.pretest01`; it is not a bound on kernel proof reduction or on the
proof-only source-core generator.

`Runtime01.candidates_length` proves that the candidate list has exactly
`treeSize S` entries: the zero-cut entry and each actual nonroot original child
edge. `candidate_count_original_edges` gives exactly `2n-1` candidates for
`n = (leaves S).length`; the edge list therefore has `2n-2` entries.
`Lemmas.mem_edges` proves both directions of actual-edge enumeration.
`Runtime01.vertex_depth` bounds every address length by `treeSize S`.

The following account follows the definitions in `Pretest.lean` and the pinned
original `RMAF.lean`. Constants are independent of tree shape and label values.

1. Building `vertices`, `edges`, and `candidates` takes `O(N²)` list work.
   At each original node, `map (side :: ·)` and append traverse at most the
   subtree vertex count; the sum of these counts over at most `N` nodes is at
   most `N²`. Every output address has length at most `N`.
2. `leaves` takes at most `O(N²)` list work, including all append copying.
   `subtree` follows at most `N` original edges. Constructing a candidate's
   `subtreeLabels` costs `O(N²)`. The literal source expression for
   `complement` can reevaluate that expression in each filter predicate; charge
   all `N` such reevaluations. Even without sharing this costs
   `O(N³ + N²b)`. Both component lists together contain at most `N` labels:
   subtree labels are a sublist of source labels and the complement removes
   exactly those labels. This is used only after the proper-input guard.
3. The guard computes two `Nodup` deciders and one `Perm` decider on leaf
   lists. In the pinned Lean toolchain, `Nodup` uses the pairwise decider,
   while `Perm` uses `List.isPerm`: one `contains` and one `erase` per source
   list element. These cost `O(N²b)` in addition to leaf-list construction.
   The exact toolchain source files are hashed by the replay receipt.
4. A candidate has one or two blocks and at most `N` labels. Each
   `partitionCheck` costs `O(N²b + N²)` even if `flatten` is rebuilt for every
   `count`; the flatten has length at most `N`. Each `restrict` visits each
   original tree node once, with a selection membership test of length at most
   `N` at each leaf, so costs `O(N²b + N)` and returns at most `N` tree nodes.
   `sameShapeCalls_bound` kernel-checks that all four potential recursive
   isomorphism comparisons together make at most the product of the two tree
   sizes in node-pair calls. Thus restriction agreement costs `O(N²(b+1))`.
5. A `rootedSpan` visits at most `N` tree nodes, produces at most `N`
   original addresses, and costs `O(N²(b+1))`, charging every selection scan,
   side-prefix map, and append. `minimalVisits_bound` kernel-checks a
   conservative envelope for `minimalVertices`: all calls to itself and its
   `rootedSpan` traversals together visit at most `N²` tree nodes. Each such
   node has at most `O(N(b+1))` local list and membership work. Hence each
   minimal embedding costs `O(N³(b+1))` and contains at most `N` addresses.
   With at most two blocks, `pairwiseEmbeddings` compares one pair of these
   lists. `disjointVertices` makes at most `N²` address comparisons, each of
   length at most `N`, so costs `O(N³)`. These are the unsuppressed original
   addresses used by the actual checker.
6. `best` calls validity once per candidate, recurses over exactly the
   candidate list, and compares only the costs 0 and 1. It does not construct
   any additional candidate or call the source-core generator. Steps 1–5
   therefore give total time `O(N⁴(b+1))` and polynomial space. Under ordinary
   bit accounting, with total input encoding length `M`, both `N` and `b`
   are at most `M`, giving the conservative bound `O(M⁵)`.

The structural bounds and exact candidate count above are kernel-checked.
The primitive-operation refinement in steps 1–6 is a mathematical source
audit, not a Lean theorem about compiled-machine runtime. A consumer requiring
that stronger formal cost semantics must still supply it. No exponential
partition, assignment, or general cut-reconstruction enumeration is hidden in
the executable pretest; `source_two_split` invokes the completed generator
only inside its erased proof.
