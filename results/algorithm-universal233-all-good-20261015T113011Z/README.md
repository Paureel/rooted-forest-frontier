# Exact all-good ForestState case

This author package supplies a finite-color tree DP, reconstructs a literal
ForestState agreement, proves minimum additional cost over all literal
checked agreements, and proves the decision result for every budget.
Fresh nonauthor proof/interface/source-cost acceptance is pending. All three
main full-algorithm milestones remain OPEN; there is no novelty claim.

Read TARGET-v1.md, INTERFACE.md, RESULT.md, and COST-MODEL.md. Replay with:

    ./bootloops-python research/rmaf/algorithm/universal233/all_good_dp/replay.py

The one-shot project replay copies pinned completed dependencies and this
package's proof sources into a new results/algorithm-universal233-all-good-*
directory. It compiles from that directory alone, inventories every actual
module declaration and axiom, checks resolved module paths, rejects false
claims and a hidden custom axiom, and catches missing audit rows, changed
origins/paths, and source corruption. It preserves earlier receipts.

`precontrols.py` was executed before universal proof and is retained for
provenance; it rewrites development output and must not be rerun after
freeze. The pre-proof set-partition enumerator is never an algorithm
subroutine. Generated files under dev/ are excluded from the immutable
manifest. After freeze, replay.py creates only new results evidence.
