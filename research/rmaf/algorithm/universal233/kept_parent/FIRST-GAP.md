# First remaining graph call

The universal untouched-parent statement has an author kernel proof. Fresh nonauthor acceptance remains pending, and all three main algorithm milestones remain OPEN.

The first unproved consuming graph call is a source-cut lift. Let `o` be any literal whole-source output, let `K` be its retained A block, and let `a` be a supplied one-cut certificate on the original restricted source tree `S|A`. The proved equality `S|K = S|A` preserves that local certificate and its local address. To insert it into the whole original source, construct an actual nonroot original S address `p` satisfying all of the following:

1. `p` represents the supplied edge of `S|A` after restriction and suppression.
2. `p` is absent from `o.sourceCuts` and lies in the residual original component carrying K.
3. Cutting `p` together with `o.sourceCuts` replaces K by the supplied local partition and leaves every other output block intact.
4. The combined cut list realizes those original components without a leafless component or redundant edge, with one additional paid source cut.

No theorem in this package constructs `p` or proves the combined realization. Theorems `every_output_retains_paid_A` and `every_output_retains_original_local_cut` establish an unchanged local problem and local payment only. They imply neither a query-budget discount nor a global completion certificate. Target disjointness and compatibility of any combined target completion also remain conditions of the later consumer.
