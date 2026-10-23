# Closed actual ordinary recursion interface v1

Import FastExact from the canonical build named in the final manifest.
Namespace: OrdinaryDispatch.FastOrdinary.

`solve q T S : Option CommonForest` is the concrete closed ordinary program.
It checks ordinary properness and the actual DepthOne0/1 pretest first. After
rejection, `early T S` inspects both orientations in common, one, high order;
it then tries Rule4 in both orientations and invokes the sealed actual
Hard2Dispatcher only when both saved cherry selectors are hard2 and both
original Rule4 selectors refuse. No baseline hard2 fallback is substituted.

Same-budget common contraction recurses on exactly one fewer target label,
including when it is selected in the reverse orientation. The runtime keeps
the explicit strict-label guard. Every paid ordinary callback tests r<q before
recursing, otherwise returning none. Termination is the lexicographic measure
(q,target leaf count). Returned reverse-orientation forests use original
agreement symmetry; common expansions restore original labels along the actual
recursion stack. The final source is the original input S.

`solve_exact q T S hp` proves OrdinaryDispatch.QueryExact for every proper
ordinary input and every natural cut budget. It has **no IH argument**.
A returned forest is an original agreement within q and has globally minimum
length among all original agreements. A none answer excludes every original
agreement of cost at most q. `solve_malformed` records the explicit refusal
outside ordinary properness. `actual_ordinary_IH` and
`actual_local_ordinary_IH` are derived conclusions of the proved recursion,
not global oracle assumptions supplied to the runtime or proof.

The sealed hard2 handler is instantiated only with `cutoff solve q`. Its
BelowIH is constructed from already proved smaller-budget queries.
Current-budget common correctness comes from the same lexicographic induction
on fewer labels. Early covers, properness, saved source priority and reverse
pretest/exhaustion facts are proved from the actual selectors.

`actual_forest_exact` supplies full-current-source-forest soundness and bounded
minimum completeness for unchanged GenericForest.solve using this closed
ordinary callback. `actual_forest_minimum` proves global length minimum for any
returned full-state forest. This includes optional targets, source forests,
and target-overlap states within the frozen forest model.

`external T S k` checks k=0 **before** an ordinary query. Otherwise it calls
solve at q=k-1 and invokes FinalCutRecovery.recover on the final forest once.
`external_exact` proves ExternalExact for proper inputs. A returned original
certificate has a realized original source cut set, original agreement,
cut-count+1 equal to component count, at most k components, and global minimum
component count. A none answer excludes every original agreement with at most
k components. `external_original_edges` gives distinct valid nonroot original
source edges; `external_zero` and `external_malformed` retain boundary behavior.
There is no implicit rho or per-recursion final-cut extraction.

The functional ordinary/hard2 integration and full-state query call are closed
at the author Lean level. This does not prove a faster-base runtime recurrence.
Actual unified callback traces, inner forest query mass, all source operations,
labels/freshmax/payload/bit growth, budget iteration and compiled-machine costs
remain external. All three main milestones, novelty, independent acceptance
and improved-base acceptance remain OPEN.
