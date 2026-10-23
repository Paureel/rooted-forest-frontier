# Author result and acceptance boundary

The all-good ForestState subcase has a complete author Lean proof. The
executable case uses a bottom-up color table with at most one candidate per
source-owner color at an internal target vertex. It returns a literal
labelled forest minimizing `ForestState.additionalCost` over every checked
agreement and gives the correct decision for every natural budget.

The proof handles arbitrary natural labels, source order, child order,
empty input, singleton source trees, and overlapping source-owner target
embeddings. It derives the original source/target topology and embedding
checks, proves the source-count offset rather than relying on truncated
subtraction, and accounts for leafless raw color regions. The converse uses
completed final-cut recovery as a proof certificate, outside the executable
DP call graph.

The pre-proof battery executed seven literal guard cases, six manual exact
minima checked by a separate small set-partition enumeration, and four false
Lean assertions. Post-proof fixtures execute the actual DP on the same
pinned cases. These are author development checks, not an independent
acceptance verdict.

The exact final receipt and declaration counts are recorded in the frozen
manifest. The source-operation argument gives an explicit polynomial and
keeps its interpretation separate from kernel-checked recurrence algebra
and compiled-machine semantics. Fresh nonauthor semantic/interface/runtime
and fresh-context prose/referee review remain pending. The parent chat
coordinates those reviews. No child agents were spawned by this author.

The package proves this case only. The complete main algorithm, its
well-founded selection, and its global runtime/recurrence remain OPEN. No
novelty claim is made.
