# Graph-route result

The universal theorem `DegreeTwoGraph.actual_degree_propagation` compiles for the
unchanged executable tree support. Given B contained in S, membership of v in
B's support, exclusion of v from B's selected occurrences, and exactly two
neighbors in S's support, it proves exactly two neighbors in B's support. The
proof derives support inclusion from completed leastness and proves that a
nonterminal in a least connected support cannot have fewer than two neighbors.
`ExactTwo` specifies the two distinct neighbors under the actual parent/child
relation. No vertices are suppressed in this statement.

The frozen independent Python checker passed all 40 hand checks, including six
specified mutations. Its bounded pilot found no counterexample in 2,488 local
cases or 2,632 agreement-partition refinements. The panel comprised 249 pairs,
2,770 selections, and separate unequal-full-label-set examples; it is not a
complete census of four-leaf labelled trees. The measured pilot time was
0.09344633299951965 seconds. The original joint-mark costs remain 1,1,1,2.

Direct Lean checks reproduce the root and suppressed-path supports, the global
three-to-four component consumer, and the degree-three negative. All six false
Lean controls fail with explicit false-proposition diagnostics. The final replay
rebuilt seven completed dependencies and the three new modules from source in
11.5428004159985 seconds. Every printed axiom set is contained in
{propext, Classical.choice, Quot.sound}. The completed dependency hashes match
the leastness acceptance record. Failed development builds remain diagnostic
records and are excluded from proof evidence.

ROUTE.md gives the ordinary graph-deletion argument and the additional
restriction/isomorphism argument needed to transport the split to the other
tree. TRANSPORT-OPEN.md states the remaining formal requirements. This arm does
not prove the general two-block existence theorem in Lean, the general unchanged
agreement-partition replacement theorem, or a `clearRest` instance. G3/G4 remain
open. Independent review, a larger search, project-wide `bootloops-check`, and
novelty review were not performed.

Read the immutable pilot and route pins before the formal receipt. The final
source is `lean/DegreePropagation.lean`; exact source/log bindings and the
rebuild commands are in `formal-receipt.json` and `README.md`. No sibling
restriction-route code or derivation was read before this report was pinned.
