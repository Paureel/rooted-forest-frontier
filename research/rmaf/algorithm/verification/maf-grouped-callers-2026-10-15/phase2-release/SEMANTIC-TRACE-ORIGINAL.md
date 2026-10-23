# Original disjoint caller: nonauthor semantic trace

Reviewed only the root-released MAF-SCHEDULER-MANIFEST-v1 package and its exact dependencies. The theorem is a conditional caller result. It does not implement the recursive exact solver.

## Executable boundary

`MafCaller.properBlock T S U` checks that the requested U is nonempty, has distinct labels, and contains only labels actually present in BOTH original trees. `slot` then literally computes `restrict U T` and `restrict U S`, runs the exact depth-zero/one source-cut pretest, stores a found forest/cost, or emits the unresolved U. `prepare` preserves Q order and stops at its first refused slot. Preparation occurs before the scheduler's budget prune.

The pretest uses no minimum oracle: it tries the uncut source and individual original source edges, checks their actual forest agreement, and selects the best accepted cost0/1 candidate. Its completed proof connects rejection to a cost-at-least2 lower bound. Finite minimum enumeration in our graph controls is only a four-label reference calculation. It is absent from the released runtime.

The runtime arguments of `prepare`, `recursive`, `attempt`, `solveDisjoint` and the scheduler contain no unknown minima or correctness-witness functions. The runtime recursive callback is supplied only the actual restricted target, restricted source and allocated budget. Our compiled callbacks contain literal tree tests and supplied witness tables. The frozen opaque-Mapping/poisoned-optimum experiment tested our Python reference runtime; source signatures and the actual compiled readout are the corresponding evidence for the Lean runtime. We do not claim that a Python metadata-access trap instrumented Lean.

## Paid scheduler and literal output

For a prepared job list, let k be the sum of stored resolved costs and p the number of hard occurrences. `schedule` rejects if q<k+2p. Otherwise every hard occurrence receives the SAME budget b=q-k-2(p-1), with Nat subtraction justified by the non-pruned lower bill. `run` preserves occurrences and order, stops after the first failed hard callback, and records that failed call as paid. Successful local calls can still be followed by a final rejection when the sum of their recorded costs exceeds q.

The original `recursive` recomputes BOTH restrictions at each dispatched U and records the actual returned F.length-1. It does not trust a separately returned claimed cost. `solveDisjoint` concatenates the actual returned forest lists via `xs.flatMap Prod.snd`; it does not select an existential optimum forest or deduplicate equal problems.

The frozen root fixture has two rejected quartet restrictions, each with reference minimum2 and a checked three-block witness. The actual caller at additional q4 calls [2,2] and returns `[[0,1],[2],[3],[4,5],[6],[7]]`. It has six blocks, additional cost6-2=4 and ORIGINAL cut cost6-1=5. At q3 it performs preparation but no recursive call. The mixed fixture stores a cost1 result and makes a budget2 hard call, giving additional3 and original cost4. The sole-hard and hard-plus-zero fixtures can call at q itself. They give normalized mass1 and establish no recursion decrease.

`algorithm-maf-grouped-fresh-review-maf-readout-v1.json` records 267 actual comparisons: original restrictions, properBlock, pretests, job problems/order, callback budgets, literal concatenation, witness validity, additional/original costs, exact problem/budget meter traces, sum of charges, and rational mass at c=2 and c=233/100. All match. No minimum tie-class adjustment was needed. Malformed original theorem guards are read out separately. The runtime is only required to refuse the explicit properBlock violations; it is not falsely required to enforce every global theorem premise.

## Universal soundness and completeness premises

`disjoint_caller_sound` assumes original target/source label Nodup, checked Q partitions in BOTH originals, and pairwise-disjoint original Q embeddings in BOTH originals. The latter two geometric guards are material: clearing source vertices alone cannot establish target agreement. The restriction selectors t/s are bound to the actual restrictions for every U∈Q.

`LocalMinimum (t U) (s U) (m U)` asserts an attained agreement of cost m U and its lower bound over all agreements. The recursive IH says every successful actual restricted call returns a valid agreement attaining m U within its budget. These are explicit proof inputs, not runtime oracle access. `prepare_planned` derives actual stored/hard jobs from the pretest and these local facts; the caller does not assume a favorable external job plan. Reconstruction uses the actual answers, their local validity, both original embedding guards, and Q ownership. It yields original agreement, F-refines-Q, and F.length-Q.length=sum m≤q. Nonempty local partitions justify all subtractions.

`disjoint_caller_complete` is relative to an already valid original agreement F refining Q with additional cost≤q. `original_minimum_lower` obtains sum m≤F.length-Q.length from the forward restriction decomposition. Local completeness is required only at the actual U∈Q and budgets with m U≤b. The theorem concludes an actual `some G` return. It does not independently conclude global validity without the soundness theorem's two embedding guards. Combining the two theorems requires all their respective premises.

`FreshConsumer.additional_and_initial_charge` is a new consuming call to the universal theorem on the completed eight-label fixture, retaining the recursive IH explicitly, and derives additional4/original5. `literal_root_forest` checks the separately frozen literal root fixture and exact callbacks. These consumers change no author hypothesis or conclusion and do not establish a general recursive solver.

## Actual original bad-parent mass

`badParents` evaluates `restrictionAgrees T S U` on the ORIGINAL restrictions. A false restriction-agreement result and an attained local minimum force m U>0: an attained cost0 agreement has one nonempty block and implies the two entire restricted trees have the same shape. The proof connects this actual bad count to the prepared job list's positive slots. A stored cost1 can pay a separate hard call; no unresolved-only bad-count assumption is substituted.

`disjoint_actual_paid_mass` then bounds the actual executed `calls`, including a failed call, by `sum_b c^(-(q-b))≤c^-1` for rational c≥2 when at least two original restrictions are bad. It retains proper original partitions, actual restriction equations and LocalMinimum facts. It needs no correctness of the arbitrary runtime callback for the trace bound. It does not supply either embedding guard needed for global reconstruction. `FreshConsumer.actual_original_mass` consumes the actual bad-parent theorem, not an unrelated abstract trace. Both rational bases have exact readouts.

## Scope

The caller's q is additional to the already cut Q. An initial original budget must also pay |Q|-1. The supplied exact recursive IH, a well-founded dispatcher, global optimum coverage across rule choices, final original cut recovery and full runtime remain open. The separate source-operation inspection is in SOURCE-OPERATION-AUDIT.md. All three main milestones remain OPEN.
