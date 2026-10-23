# Whole QUERY value, projection and source occurrences

This is the completed AUTHOR mathematical argument for QUERY, supported by the checked local Lean proofs named below. It is not a Lean theorem formalizing the entire projected runtime, an independent verification, or a cost theorem. The v2 peer/status exposure and v3 accidental one-line theorem contact remain permanent; the contacted appendLabelsMeter_value proof is not used. Root continuation v4 permits this exposed author route only.

The implementation is exactly the public mathematical base manifest ae6b35f2235de3a9a76435467bd2bd7405129b9199ab2175a1a49fb9e9b4fcff plus additive projection amendment manifest 61da6acaa2765a4802359ae8da79f9e35bce78c6f1ef9ce8cfe25db175a41458. In particular it uses the fixed QUERY and PAID bodies, all named retained procedures and diagnostics, and the amendment's two additional qualified coloring omissions. The original v1 defect stays frozen. No machine, source definition, value callback, fee convention or representation is changed here. OPTIMIZE/recovery and operation/word/space counts have separate owners.

## Statement and minimal occurrence specification

Write B(q,T,S) for the canonical OrdinaryDispatch.FastOrdinary.solve q T S. Its exact defining computation was released in v22, without termination or theorem bodies. Write

    t(q,T,S) = ordinaryStepTrace (fun r U V => B(r,U,V)) q T S.

The trace definition is the exact v24 WorkRecursion declaration. Positions in its stored queries list, starting at zero, are SOURCE query slots. They are positions, not query values. Equal arguments at different positions are different slots.

For every finite T,S and natural q, including improper inputs and q=0:

1. Fixed projected QUERY(q,T,S) has a finite execution and returns B(q,T,S).
2. At each actual QUERY body, every immediate recursive QUERY invocation has an injective map to a position in t(q,T,S).queries. The mapped slot has exactly the invocation's two decoded trees and budget. Its ordinary return is the invocation's actual None/Some forest; where a scheduler stores a cost/answer pair, that pair is exactly Option.map (fun F => (length(F)-1,F)) of that return.
3. The map preserves multiplicity. A failed live call returning None has its own position. A PAID invocation with residual r>=q makes no recursive QUERY invocation, even if a corresponding SOURCE slot is present. Such refused slots retain live=false and returned=None in the auxiliary ledger; they need not lie in the image. No bijection between stored SOURCE slots and executed QUERY bodies is claimed.
4. Prefixing the mapped position to the child map gives an injective map from all recursive QUERY body occurrences to finite SOURCE slot-address paths. At every prefix the state, arguments and return agree with the corresponding canonical source query. This is a call-tree injection, not a monotone chronological map into a flat trace.
5. The retained projection of every reached procedure result equals the declared projection of the corresponding source result. It includes all retained constructor tags, branch decisions, budgets, cuts, output/receipt data and diagnostics. Value-producing ordinary/forest callbacks have their original actual order and their actual argument/return occurrences. Only the explicitly enumerated accounting/frontier replays and the two amended coloring fields are omitted.

An occurrence stores (parent body occurrence, local lexical/list ordinals, target, source, residual budget, live flag, actual option return). The ordinals distinguish duplicates independently of equality of trees, outputs or returned forests. No heap address identity is part of this statement. A stored query tuple alone is not enough to distinguish occurrences; its list position or the proved unique composite label is required.

## Joint well-founded induction: discharging the worker premises

Use lexicographic rank (q,length(leaves(T))) for ordinary QUERY. Strengthen the induction assertion to all five statements above, together with a finite retained execution derivation. Inside a fixed ordinary body, use strong induction on the forest routine's budget b, and structural induction on its finite branch/job/child/output lists and tree generators. This is an induction over the supplied finite procedures, not a new interpreter or framework.

Fix q,T,S and assume the strengthened assertion at every smaller ordinary rank. For this parent ONLY, interpret a local graph's OrdExec predicate by

    R(U,V,r,a) iff a is the result of a finite fixed projected QUERY(r,U,V)
      and [r<q or (r=q and length(leaves(U))<length(leaves(T)))].

The outer induction hypothesis proves sound: every R(U,V,r,a) has a=B(r,U,V). It also proves enabled totality for every PAID callback: enabled(cutoff(q),r)=true is exactly r<q, so the needed finite child execution exists and satisfies R. These are proved induction facts about the actual fixed recursive execution. They are not supplied runtime oracles, an assumption of soundness for unrestricted executions, or a global cache.

COMMON is the one exception to the PAID totality interface. It uses the actual constructed pair p and the literal strict comparison length(leaves(p.first))<length(leaves(T)). When that comparison fails, construct CommonExec.refused. When it holds, the same-budget child has strictly smaller second coordinate; the outer induction hypothesis gives its actual execution and return, and CommonExec.returned applies directly. The overly broad generic common_exists premise is not instantiated with R for arbitrary trees and budgets.

For the forest subinduction, the concrete ForestExec graph has already been defined and checked. Improper, agreed, absent-target and no-job cases use their literal finite branches. A singleton invokes PAID at the displayed budget and uses the enabled-totality fact just proved; a refused cutoff returns None without a child body. The no-overlap case constructs the exact finite jobs and executes the scheduler at its computed allocated budgets. Resolved jobs make no callback. Unaffordability and a failed hard return stop at their literal tests; a successful hard return processes the remaining tail. Every reached enabled ordinary callback is an R instance.

For overlap, process every generated left output and then every generated right output in the literal concatenation order. For each eligible output, d=length(sourceCuts) has 1<=d<=b, so b-d<b. Invoke the forest induction hypothesis on exactly its replacement forest at b-d, even if its eventual answer is None. Continue with all later eligible outputs. An ineligible output makes no recursive forest invocation. Structural generator/list finiteness and this strict b decrease establish finite execution, returned values, debit/frontier observations and occurrence ledgers simultaneously. Equal generated outputs keep different ordinals; no call is memoized or coalesced.

Apply SourceForestV3.forest_exists, forest_correspondence, children_source_fields, children_index, forest_slots_realize and children_slots_realize to these actual smaller executions. The enabled-totality and sound premises in all larger named worker graphs now follow from the induction hypotheses. Their finite list inductions construct Children, Rule4, every Good/Hard/Bad path, grouped/literal schedules and all Rule5 caller graphs. The frozen ORDINARY-TOTALITY-INDUCTION-v3 contains the same termination argument; the present induction also proves its semantic conclusions.

## Exhaustive ordinary body cases

The checked SourceOrdinaryFrontV3.front_value evaluates the exact meterFront value using only licensed pure primitive VALUE interfaces. It gives the same properness, pretest and early discriminator as the v22 defining computation of B. All retained pretest/selector diagnostics and eager work are covered by the finite projection induction below; an equality of just the discriminator does not authorize deleting them.

|Reached body case|Actual return and exact SOURCE stored queries|
|---|---|
|Improper; pretest Refused; pretest Found|The literal stop value agrees with B's same branch. Found still constructs its forest before affordability. There is no recursive QUERY body and the trace query list is empty.|
|Common(reverse,c)|The construction and expansion identities in CommonProjectionV3, common_raw_value and actual_common_trace identify the actual returned option and the zero-or-one exact query slot. The preceding strict leaf comparison supplies the smaller-rank child.|
|One(reverse,c)|SelectedChildrenConsumerV3.actual_one_step gives the exact ordinaryStepTrace value and indexed queries. OrdinaryChildrenCanonicalValueV3.one_parent_raw identifies the actual parent OrdinaryDispatch.runChildren consumer, rather than treating the distinct Rule5 child function as an alias. children_slots_realize preserves every callback return.|
|High(reverse,c)|The same statements are high_actual_trace/actual_high_step and high_parent_raw, with the actual three-child list and its order. All retained agreementChecks, successful/failed child outcomes and affordable-child call records remain.|
|Rule4Forward or Rule4Reverse|Rule4ConsumerV3.rule4_actual_trace supplies the full return and stored queries for the selected orientation. AnswersExec runs the tail first, then rule4StateMeter even on refusal, then the affordable forest. Rule4OccurrenceV3 and Rule4BijectionV3 give unique (branch ordinal,inner slot) labels and explicit inverse maps between the actual tail-first and recorded head-first ledgers.|
|Hard2(c,d)|Hard2WholeLedgerV3.hard2_trace_ledger gives the whole Hard2Receipt value and exact recorded queries; frontend_trace_cases proves the actual selected route agrees with hard2Trace in every graph/partition/restriction case. hard2_canonical_value identifies its value with the actual Hard2Dispatcher.run consumer, including retained d at the ordinary selection boundary.|
|Early Refused|The literal return is None and the stored query list is empty.|

These cases exhaust front/early, and are exactly the v22 B and v24 ordinaryStepTrace branch tables. Replacing each reached smaller recursive result by the induction hypothesis therefore proves QUERY(q,T,S)=B(q,T,S), not merely equality to another supplied answer callback. The canonical defining computation is used mathematically once per case; it is not executed as an oracle by QUERY and no saved whole-solver equation proof is used.

The Hard2 case is fully concrete. Its refused/direct arms have empty callback ledgers. Its disjoint arm uses actual units-before-query execution and the exact raw return/stored-list correspondences in DisjointRawTraceV3; the auxiliary raw helper's query-before-units evaluation is not a physical-order identity. Its admitted Rule5 arm uses DispatchExec through all prefix, first, third, remaining-one and remaining-second callers, including full setup, guarded/outside/paid execution and failed builders. Rule5CanonicalRawValueV3 supplies the exact caller/dispatch answer binding, without making outsideReply or reconstruct an oracle. The primitive reconstruction check is the actual measuredAgreement value, as proved in the earlier raw common seal.

The paid Hard2 arm uses PaidCaseRawProjectionV3: Empty, Good, Hard and both Bad variants are bound to paidCase and then the canonical combine. Good uses the actual owned/local-target/DP/additionalCost and affordable residual forest. Hard evaluates every literal output with the tail-first fullOutputsSource chronology. Local BothBad executes its actual entry dispatch then the entire tail; grouped BothBad preserves its OutputResult tag, full scheduled Receipt (answers,calls,visits), and ordered queries through OutputRetains, output_retains and trace_eq. Their raw QueryWork bills 5/8 are not identified with the source literal-32 accounting. The paid case is evaluated before unit children, while the stored calls are units++paid. The earlier full-output and paid-unit composite occurrence labels, inverse maps and permutations preserve every duplicate and every slot's complete data at both seams.

## From the local ledgers to exact SOURCE positions

At the fixed parent, sound for R is now available. All linear cases have

    slots.map (fun s => (s.index,s.query)) = indexFrom 0 t.queries.

ledger_strict, ledger_member and the exact projection of indexFrom give distinct indices in the range of t.queries, and recover the tuple at that exact index. SlotRealizes states either a literal refused cutoff with live=false and returned=None, or live=true together with the actual R child and its mapped returned cost/forest pair. Thus every actual immediate child body maps to its live slot index. COMMON's mode is direct and its sole possible child has the separately proved leaf decrease; all other callbacks inherit cutoff(q).

For Rule4, full-output and paid-unit seams, use their two labelled ledgers. There is a permutation from chronological labelled occurrences to recorded labelled occurrences, with explicit inverse maps preserving the entire label and Slot. The recorded labels are pairwise distinct. This ensures that the labelled-element subtype contains every occurrence exactly once; equal argument tuples or equal answers never collapse it. The recorded query projection is the exact canonical stored list, in its source order.

Hard2WholeLedgerV3 combines these facts for the actual frontend route. Its RouteLedger constructors retain the specific chronological ledger from the executed graph; in the paid case this is paid-before-units, not an arbitrary choice of a permuted list. Hard2RecordedPositionsV3.recorded_positions proves the explicit mathematical position map

    position : {o | o belongs to chrono} -> Fin(length(rec)),
    injective(position), and rec.get(position(o))=o.

The theorem live_recorded_positions restricts this injection to live occurrences and retains enabled=true, the actual child execution and the exact returned pair. The further checked theorem live_source_positions takes rec.map(query)=t.queries and returns an injection directly into Fin(length(t.queries)), with t.queries.get(position(o))=o.query and the same actual return witness. These position functions are mathematical witnesses; the runtime has no corresponding search, address table or cache. The same finite list-position argument applies to the earlier labelled Rule4/full-output lists; their checked inverse maps identify which recorded occurrence to use. Their physical order may differ from stored order.

To compose globally, give the root the empty address. If a child invocation at actual node u maps locally to stored position i, give it source address address(u) followed by i. Append the child's own mapped address for each descendant. A finite actual execution tree exists by the joint induction above. Its source addresses follow the exact t-query tuple at every step, and the child return is B at that tuple by the child induction hypothesis. If two actual body occurrences first diverge at siblings, local injectivity gives different next positions. If one is a proper ancestor, their address lengths differ. These are the only possibilities for two finite tree paths, so the global map is injective. Including the root if desired preserves injectivity by the empty address.

Refused PAID evaluations are finite local operations; they are never silently made into recursive QUERY bodies. Their SOURCE slots, and any other analysis-only source occurrences outside this image, remain available in the full source sum. For any nonnegative weight on stored slots, the sum over the image is at most the sum over all stored slots. Permutations preserve every sum depending on the entire preserved Slot, as already checked locally and in recorded_sum. This is only the occurrence/nonnegativity fact needed by the separate source-counter induction, not an operation or RAM-fee bound.

## Closing the retained projection premises

ACTIVE-PROJECTION-PRESERVATION-v3 proved the finite local statement conditional on reached recursive retained returns/events. The present induction supplies those returns and events from actual smaller executions: use the outer hypothesis for COMMON/PAID and the inner b hypothesis for forest overlap. All remaining recursion is finite structural evaluation of the exact named bodies. Therefore that local result applies at every reached node and proves statement 5 without an external recursive premise.

Every retained field still has its original producer. Source record constructors project exactly the finite field list, unboxing only wrappers with one remaining value field. All other fields, including failed tags, Child.paid, Entry.budget, scheduler cost/visits, sourceCuts, ownership/colors, candidates, checks/tailSizes/comparisons, calls/queries and all retained output receipts, are computed and kept. In particular Rule4 states run before affordability, full-output tails run before heads, paid computation precedes units, and eager selection/check lets remain eager. The additive coloring amendment removes exactly Built.coloring and InitialMeasured.coloring; actual Group.color, marked/fresh labels, both original leaf traversals and all guard data remain.

The omitted forestWork/debit/C and enumerated ordinaryCalls/frontier replay computations are analysis only under this explicit implementation. They are not silently deleted from the old frozen literal-runtime model, and none is replaced by zero or an external cost answer. Their omission does not assert equality of a returned register to C or equality of all naively executed accounting callbacks to runtime events. The retained value-producing forest/ordinary calls have the injection just proved. This closes the semantic/projection obligation for fixed QUERY and leaves the separate local-operation/log-cost, numeric-width/address/space, optimizer/recovery and independent verification obligations intact.


[The following author execution/control outcomes are omitted from this argument-only copy. No independent acceptance is conveyed by this argument.]
