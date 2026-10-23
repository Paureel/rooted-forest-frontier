# Budget optimization author interface v1

Status: author proof and development controls only; fresh nonauthor acceptance pending. Global 2.33 runtime, improved-base acceptance, and novelty remain OPEN.

The new Lean namespace is `OrdinaryDispatch.BudgetOptimization`. Import `BOConditional` (or `BOControls` for tiny controls) with this package build first and the canonical licensed FastOrdinary build second on LEAN_PATH. No frozen dependency is rebuilt.

`optimize T S : Execution` checks the original ordinary input, runs `scan (fun q => FastOrdinary.solve q T S) 0 n`, and invokes `FinalCutRecovery.recover S F` once after choosing the first successful budget. Here n is the original target label count. `Execution.search.trials` retains budget and literal answer at every call, including failed calls; `recoveries` retains the final forest and recovery answer. The runtime does not call an optimum/partition oracle or construct a singleton/exhaustive fallback. The singleton forest in BOForest is a proof witness only. The constructors of Tree are proper rooted binary trees, and properness checks distinct equal labels; there is no implicit rho.

`BOScan.scan_success` proves the exact trial list `failedTrials start skipped ++ [(q,some F)]`, the successful query equation, every earlier query refusal, and the finite budget bound. `failed_budget_trace` identifies the failed budget list as `List.range' start skipped`. `scan_failure` retains the complete refused prefix. Termination is structural recursion on remaining length.

`BOOptimize.scan_upper_success` constructs the singleton agreement in proof and uses frozen solve_exact to ensure success by n-1. `selected_minimum` proves F.length=q+1 and global minimum from the actual successful query, using all earlier failed queries to rule out an oversized first-success budget. `optimization_exact` proves original agreement, realized original cuts, distinct valid nonroot edges, cuts=q, components=q+1, global minimum, the full failed/successful trace, and exactly one recovery. `actual_query_count` gives q+1 queries, q failures, one recovery. `malformed` gives zero queries/recoveries and no output. `external_zero_guard` preserves the frozen external k=0 convention; optimizer q=0 remains valid.

`BOCost.total_charge_exact` charges every actual query trial, the printed wrapper interface, and precisely one final meterRecover. `decision_sum_bound` proves the full sum bound for c>1 under nonnegative monotone P and per-query costs <= P(q)c^q. It uses the conservative polynomial factor q+1; no failed call is dropped. `all_work_bound` also exposes an explicit final recovery bound for arbitrary c>1. The completed frozen recovery interface supplies 2^q, hence automatic absorption requires c>=2. `finalPolynomial_uniform`, `recoveryPolynomial_envelope` bind this one final call at the actual original agreement and replace forest sizes by an explicit degree-eight polynomial in the original n.

`BOConditional.conditional_k_bound` and `conditional_233` compose the exact returned output and k=components>0 conversion with the entire bill. `conditional_233_polynomial` makes every coefficient explicit. With query coefficient A(n+q+L+1)^d and wrapper envelope M=B(n+L+1)^e, the full bound is

    [ n A(2n+L+1)^d + (M+Mn+M) + recoveryEnvelope(n) ] (233/100)^(k-1).

The hypotheses are real obligations, not completed work: queryWork w must be a cost of the actual frozen solve, including recursive operations and current/fresh labels and payloads, and the three M charges must cover properness/leaf count/encoding, each local trial's let/match/successor/retained cons, and final selection/record construction. Source-operation envelopes do not independently certify compiled-machine bit cost.

FIRST MISSING CONSUMER: an actual FastOrdinary.solve source/bit work theorem supplying `perQuery : forall b, b<n -> (w b : Rat) <= queryPolynomial n b L A d * (233/100)^b` for every budget including unsuccessful decisions, plus the actual primitive-cost interpretation of w and wrapper charges. No unfinished main/child/reviewer source was opened to supply it.

Licensed dependency reuse is same-lineage development. The root will stage fresh nonauthor verification. This package cannot be advertised as a completed global 2.33 runtime theorem.

`external_at_selected` additionally equates the optimizer's actual output with the frozen external API at k=q+1. `conditional_233_correct` composes original-certificate validity and global optimality with the conditional bill for that same deterministic returned output. To infer asymptotic O, A,d,B,e must be uniform constants over the input family; per-instance fitted coefficients do not establish an asymptotic bound.

Canonical source/olean receipt is the one pinned by FINAL-MANIFEST-v1.json. The build directory is disposable development staging and may contain earlier pilot versions. LATEST-REPLAY-v1.json is an operational pointer, not the frozen identity. Replays create new result directories and never rebuild the licensed package.
