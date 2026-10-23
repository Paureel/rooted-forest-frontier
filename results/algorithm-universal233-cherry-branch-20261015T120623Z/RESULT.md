# Ordinary cherry branches

The author proof establishes actual ordinary t1 safety and t>=3 branching
safety from original rooted agreements. Fresh nonauthor verification is pending.
The complete faster algorithm, its global runtime, and its novelty remain OPEN.

For a proper original rooted target T with an actual cherry a,b and an original
source S on the same labels, `cuts S a b` lists the original directed child
edges leaving the unique a--b path. Every address names the original child,
including original vertices suppressed in a displayed restriction. The list
contains no edge above the LCA and introduces no root taxon.

`actual_pendant_safety` proves, for every original agreement F, singleton a or
singleton b or refinement of the literal source partition after all t cuts.
`source_embeddings`, `pendant_partition_check`, `partition_length`,
`cut_component`, `root_component`, `original_cover`, `roots_separated`,
`cut_leafset`, `root_leafset`, and `no_leafless` construct the original
leaf-bearing residual forest for arbitrary t. Thus t>=3 uses costs (1,1,t).

Strict refinement of every original F fails for t1. The preserved example is
T=((0,1),2), S=((0,2),1), F={{0,2},{1}}. Both F and the replacement
G={{0,1},{2}} are original agreements of size two; only G refines the pendant
partition {{2},{0,1}}. `actual_t1_pendant_exchange` proves the universal
no-larger original-agreement replacement under exact one-pendant geometry.

The t1 proof splits every original agreement block at the one original source
subtree. The split preserves original topology and embeddings and adds at most
one block. `core_has_cherry` proves that the root remainder contains the actual
rooted cherry, including arbitrary siblings above its original LCA. If the
original endpoint alternative gives a singleton, that singleton survives the
split; actual common-cherry reassignment saves exactly one block. Literal
state transport returns an original agreement refining the source partition.
If F already refines it, the proof returns F. No exchange/refinement/ownership
premise is supplied by the caller.

`actual_t1_two_minimum` gives the requested cost-(1,1) two-child rule under
child-specific exact solver hypotheses. `actual_t1_deterministic_minimum`
proves the stronger deterministic pendant rule stated in the retained baseline.
`actual_t1_two_budget`, `actual_t1_decision`, `actual_high_budget`, and the
bounded child-solver theorems connect these rules to executable child states
and exact remaining budgets. These are conditional local consumers; no
recursive solver, termination proof, or improved full running time is claimed.

`cherries` is a finite original-address enumeration, with soundness and
completeness. `select` materializes all opposite-source cut candidates and
checks common, t1, t>=3, then hard2 priority. `selected_spec` proves the selected
count and all preceding rejected-count conditions. `SourceBranches` records
the endpoint's actual original terminal edge and the full pendant edge list.
Its endpoint graph theorem identifies the isolated original leaf, the root
remainder, and a leaf in every residual region.

All imported proof packages are declared development contacts. The final
receipt audits actual module origins, including private/generated declarations,
with only standard axioms. It tests true and false controls, missing audit
rows, source pins, a wrong local module path, and a concealed private custom
axiom. These author checks do not replace fresh hostile and nonauthor work.
