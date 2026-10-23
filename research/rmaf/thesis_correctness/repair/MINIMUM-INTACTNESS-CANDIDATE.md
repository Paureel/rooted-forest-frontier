# Candidate consequence: minimum completions preserve common subtrees intact

Status: derived candidate, not fresh-reviewed and not used by the delivered exchange chain. It is retained as a possible next step toward the contraction interface. No novelty claim.

Suppose A is a proper pendant subtree that is identical in two compatible current finite binary forests. Let E be globally minimum among their actual AF cutsets, rather than minimum among extensions of prescribed cuts. The proposed consequence is that E contains no edge strictly inside A.

At each internal vertex w of A, its two whole child subtrees are common sibling subtrees in both forests. Set E2 empty. The proposed strict empty-common-subtree repair ensures that their root fragments survive E; labelled child roots survive automatically. The reviewed full-path normalization can therefore be applied to the two-edge child path. If E cuts either of those edges, normalization restores one cut for no new cut, or restores two and adds at most the actual incoming edge of w. In either case it produces an AF with strictly fewer cuts, contradicting minimum cardinality. Every internal edge of A occurs in one such child pair.

This argument uses the exact local normalization and minimum-fragment statements, including their actual AF compatibility and proper-subtree hypotheses. It does not yet prove the expansion/contraction bijection or the general protected-origin lift. A fresh checker must assess the corollary before it is used as a forest fact.

The candidate was frozen in common-subtree-minimum-candidate.json before execution. The earlier controlled raw-edge oracle found no counterexample in all9 ordered three-leaf and225 ordered four-leaf input pairs:21 and759 minimum raw cutsets respectively, with6 and153 nonvacuous common-subtree/minimum checks. The fixed common-cherry control had optimum1. The stronger statement for arbitrary AF cutsets was deliberately rejected by a singleton-producing cutset. These are author-generated finite checks on connected original inputs, not a universal proof or another independent review.

Receipt: [candidate check](/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/thesis-correctness-repair-common-subtree-candidate.json).
