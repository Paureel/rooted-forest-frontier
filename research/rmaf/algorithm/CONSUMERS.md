# Algorithm consumer/import trace v1

Read 2026-10-14. These records restrict imports; they do not discharge them.

| Named algorithm call site | Candidate import | Required hypotheses | Current ruling |
|---|---|---|---|
| Hard child with a common edge in three parent embeddings | Baseline Lemma1 splitting cores, pp7–8 | Nontrivial label bipartition; maximum undirected degree3; coverage by partition refinement; emitted cut cost and lazy polynomial overhead | Retrieved source statement; no formal core construction theorem admitted yet |
| General overlap fallback | Baseline Lemma2 SPLIT, p9 | Shared edge; each parent source component has labels on both sides; descendant cut-core covers every avoiding partition | Retrieved; cannot silently substitute literal edge inclusion for label-partition refinement |
| Isolated homeomorphic overlap group | Baseline Lemma15 rule7, p24 | At least2 homeomorphic components; no overlap with any outside component | Retrieved; polynomial Fitch implementation/realization/reconstruction and formal correctness still required |
| Disjoint forest decomposition | Baseline recursion rule pp9–10 | Parent embeddings pairwise vertex-disjoint; charge component pretests and all failed local-query budgets | Retrieved; keep p=1 `T(q−1)` separately from p≥2 `pT(q−2(p−1))` at t=1 |
| Compatible/triple terminal detector | `triple_dp/PROOF.md`, Statement and G1–G3 | Every component compatible with target restriction or has exactly3 labels; no-rho refinement; graph/DP and executable correspondence | Conditional/open; finite tests and generic table proofs do not close G1–G3 |
| Pure-bridge marked terminal/elimination | `pure_bridge/FORMAL.md`, G1–G7 | Path-convex actual embeddings; pure degree-two overlap; global one-cut clearRest preserving all old marks; common partition-family and paid role swap; exact marked minimizer | Conditional/open; do not replace global repair by additive independent mark penalties |
| Degree-two global repair inside a cover | `progress/bridge-degree-two.json` and actual final review receipts | Nonterminal occupied degree-two subpiece, exact original supports, restriction transport, agreement partition, old marks | Final nonauthor release pending; no unconditional import |
| Four-transition compatible/triple family automaton | `triple_dp/family/INTERFACE.md` and final receipts | Retained labelled convex families; leafless open normalization; complete merge and reverse restriction/reindexing; exact tolls | Normalization/forward/three-operation scoped statements reviewed; full correspondence open |
| New global balanced safe-cover integration | `sources/previous-work/RESEARCH.md` §8 lines230–246, root-written SAFE-COVER-TARGET.md | O*((5/4)^b) generation/count; ≤b paid nonredundant precuts; preserves at least one original optimum; every state terminal-class admitted; pure-bridge unmarked tau≤b/2; all marked-query and role-swap costs paid | Source research target, not a theorem; independent root-dispatched global separator route active. A one-color unchanged full-budget local query does not meet the balance payoff |

Every new route must add its actual consumer hypotheses here or in a route-local
trace. A library's compiled theorem count is not an admission criterion.

Read previous-work RESEARCH.md Lemma4.1/Corollary4.2 in this session: marked
piece optimum h_D(J) must be converted to the role-swapped additional-cut
budget q_J=h_D(J)−(r−1)≤d_D. The second bounded query is
mu−(r′−1)≤d_D, with negative budget immediate failure. The source argument
requires the exact common feasible partition family and realizable r−1
region cuts. A bound on marked pieces or h_D(J) by d_D+r−1 is not itself
the residual FPT budget; count and execute the conversion at the call site.
