# Hard2 paid caller: author extension

Import PaidValidity. Namespace Universal233.Hard2PaidLocal.

runHardPaid actual T S q c out uses the actual candidate's two original cuts,
selects the frozen literal output list and its literal permutation, and calls
runOutputs. The edge family keeps the first parent when restrictionAgrees S T
first is true; otherwise it keeps the second. It retains all list occurrences,
pays each output's entire original sourceCuts length, materializes its complete
source forest and calls GenericForest.solve actual at the remaining budget.
The original agreement/budget checks and least-answer choice are unchanged.

actual_paid_conditional_cover takes proper input, the actual forward hard2
selection, runHard2 = some out, actualPaidCase and BelowIH q actual. It covers
every original agreement F refining CherryBranching.pendantPartition within q.
actualPaidCase excludes disjoint, requires the literal first-or-second good
parent test for edge, and is True for clique, four, diagonal and vertex cases.
The geometric guards come from the checked selector. Direct list/pair covers
are used; no singleton alternative is used as a paid-only cover.

actual_paid_sound is unconditional. actual_paid_minimum compares the returned
answer against all bounded original agreements refining that original parent
partition. It does not assert that the returned answer itself refines that
partition. The outer hard2 combination handles singleton alternatives.

actual_paid_full_source_call derives each called output's source partition,
source embedding, original-cut realization, component/cut count, cuts >= 2,
full payment and complete source forest. actual_paid_calls_strict proves
budget + 2 <= q and budget < q. actual_paid_trace_mass bounds all retained
forest calls by the frozen raw family mass: 3*c^-4 for clique; 4*c^-4 for four;
c^-3+c^-4 for diagonal and vertex; c^-3 for edge. These are full-source forest
calls; their inner ordinary frontier and work bill remain separate obligations.

All inputs are completed frozen author sources, including this author's prior
selector and BelowIH locality releases. This is DEVELOPMENT reuse, independent
credit zero. Main algorithm, base cases, correctness of the complete dispatcher,
source/bit/payload cost recurrence and novelty remain OPEN. The c=2.33 target
remains conditional, with q=k_opt-1 and no implicit rho.
