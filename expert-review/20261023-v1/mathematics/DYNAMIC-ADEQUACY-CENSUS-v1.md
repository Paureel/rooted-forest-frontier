# Actual body to constructor census

The runtime is the frozen mathematical base ae6b35f2235de3a9a76435467bd2bd7405129b9199ab2175a1a49fb9e9b4fcff plus additive projection 61da6acaa2765a4802359ae8da79f9e35bce78c6f1ef9ce8cfe25db175a41458. Module/line references below identify literal bodies inside the licensed PROCEDURES-v1.md; they do not authorize reading adjacent original files. Constructor references name OWN graph files. These are finite cases of the actual bodies, rather than appeals to graph existence theorems.

Fix a parent QUERY(q,T,S). Its ordinary callback is the actual fixed PAID(q), except for the direct COMMON child. For a subevaluation E, A(E) is its ordered list of local PAID/direct-ordinary attempts. Each entry contains its own dynamic ordinal, exact two trees, budget, option return and live flag. An enabled attempt contributes one immediate QUERY body; a refused cutoff contributes no QUERY body. Thus the actual immediate body list is live(A(E)). An entry returning None can be live. Descendant bodies are inside the invoked child's evaluation and are composed later by source-address prefixes.

In the tables, H and R mean the attempt lists from the particular actual head and actual tail evaluations. '+' means ordered list concatenation. A graph's numeric work/debit fields are mathematical decorations filled by its constructor formulas, never assumed runtime inputs. Equality of retained returns uses the exact declared projection, not equality of those deleted numeric fields.

## Terminal ordinary call sites

|ID|Exact retained call site|Construction from the actual call|
|---|---|---|
|D0|CommonBranchWork:14, rec q p.first p.second|After the actual strict leaf guard, keep that particular child evaluation and use SourceCommonV3.CommonExec.returned. Failed guard uses refused and no call.|
|D1|ForestProgram:30, ordinary t s b|Inspect the actual PAID(q) guard at this invocation. Off gives SourceForestSingletonV2.Invoke.refused; on keeps that actual child return in Invoke.returned. Then ForestExec.singleton.|
|D2|ForestDefs:43 closure, invoked at QueryCaller:38|The closure invokes PAID(q) on p.first,p.second,b and maps its actual return to (length(F)-1,F). Off gives SourceCouplingV2.Run.refused. On gives SourceDisjointV2.PairChild.returned with the actual child, then Run.failed or success according to its actual mapped return.|
|D3|CommonPaidSource:29, cb j.T j.S j.budget|Construct Invoke.refused/returned from this actual guard/evaluation, then SourceRule5CommonJobsV3.JobsExec.cons. Continue with the tail even when this return is None.|

These are the four caller sites reaching the ordinary binding in the fixed QUERY dependency graph. The shared PAID forwarding body is listed as P0 below; it contributes the entered child of D1,D2 or D3, rather than a second body for the same attempt. The complete callback-forwarding cases are enumerated below. The runtime closures at these sites are fixed by ALGORITHM/PROJECTION; there is no supplied answer callback. Generic map/filter/find/best/scheduler functions receive only the displayed fixed predicates/adapters. The closed primitive families in the final table contain no further ordinary invocation. The source accounting and frontier procedures excluded in the final table are not runtime callback sites.

## Entry, COMMON, forest and children

|ID|Actual body and exhaustive discriminator|Existing constructor(s); exact attempt order|
|---|---|---|
|P0|CutoffFacts:5..6 / PAID(q,U,V,r): actual r<q comparison|False returns None with live=false; true evaluates exactly one actual smaller QUERY with live=true, in whichever D1/D2/D3 caller invoked this closure. ActualCaller.actualCallback:24 and completeBranchSource/completeRouteSource bind this closure. Constructing or forwarding the closure makes no ordinary invocation.|
|E0|ordinaryCompleteStepSource:21..24 / QUERY: evaluate meterFront; Stop or Selected|Stop has no graph child and A=[]; Selected executes exactly one branch below. front, pretest and Early execute all retained diagnostic computations.|
|E1|completeBranchSource:10 / CommonBranchWork:11..19: build pair, measure both leaf lists, compare|CommonExec.refused when the strict comparison fails; returned with the actual D0 child otherwise. A=[] or one direct live slot. The child's actual None/Some controls expansion; expansion has no ordinary call.|
|E2|completeBranchSource:11,12: One/High in either orientation|Construct the actual Oriented pair and pendantChild/branches list. Apply the child cases C0..C2 to that exact list. finishOne/finishHigh and final best/accepted computations add no calls.|
|E3|completeBranchSource:13,14: Rule4Forward/Reverse|Use the actual selected typed choice and R0..R2 below. Reverse changes the selected choice's tree parameters; it does not change the rule's tail-first evaluation.|
|E4|completeBranchSource:15,16: Hard2 or Refused|Hard2 uses H0..H4; Refused returns None with A=[]. These cases exhaust the Early datatype.|
|F0|ForestProgram:26: proper=false|SourceForestV3.ForestExec.improper with that actual false equation; A=[].|
|F1|ForestProgram:27: proper=true, agrees=true|ForestExec.agreed with those actual equations; A=[]. Both separately written ss.map(leaves) traversals remain.|
|F2|ForestProgram:28,29: proper=true, agrees=false, target=None|ForestExec.absent; A=[].|
|F3|ForestProgram:30: target=Some(t), sources=[s]|Use D1's actual Invoke and ForestExec.singleton. A is its one attempted slot; checked/bind adds no ordinary call. A live None return is retained.|
|F4|ForestProgram:31..33 / ForestDefs:33..43: nonsingleton, overlap=None, jobs=None|Evaluate component restrictions and pretests in the literal jobs recursion. Its actual None gives ForestExec.noJobs with all five actual test equations. A=[].|
|F5|Same branch, jobs=Some(js)|Use S0..S4 on that actual js and construct ForestExec.disjoint. Flatten and checked occur after scheduling and add no ordinary call. A is the actual scheduler attempt list.|
|F6|ForestProgram:34..39: overlap=Some(h)|Build actual left generation, then actual right generation, map their original indices, append, execute B0..B2; construct ForestExec.overlap. Final best/accepted is closed. A is the branch attempt list.|
|B0|ForestProgram:35 filterMap, empty branch list|BranchesExec.nil; A=[].|
|B1|Head io, actual d=length(io.sourceCuts) fails 1<=d and d<=b|BranchesExec.skip with the negated actual predicate and actual tail graph; A=R.|
|B2|Same head passes both inequalities|Construct actual recursive FOREST at the actual replace result and b-d, then actual tail; BranchesExec.take. A=H+R; the tail is reached even if the child returns None. None omits an answer cell, not the attempted calls.|
|S0|QueryCaller:49, actual q<knownCost(js)+2*pending(js)|SourceForestV3.ScheduleAt.refused; A=[]. The known-cost and pending traversals still run.|
|S1|Schedule affordable|Compute actual allocated, execute S2..S4, then actual answerCost acceptance; ScheduleAt.run. A is unchanged by the final acceptance. Raw bills and graph bills are not identified.|
|S2|QueryCaller:33, empty jobs|SourceCouplingV2.Run.nil; A=[].|
|S3|QueryCaller:34..36, resolved head|Run.resolved using the particular actual tail; A=R. Prepending stored data/visits has no ordinary call.|
|S4|QueryCaller:37..42, hard head|D2 off -> Run.refused, one nonlive slot and no tail. D2 on/None -> Run.failed, one live failed slot and no tail. D2 on/Some -> Run.success with actual head and actual tail; A=head-slot+R.|
|C0|ChildrenExecutionWork:33, empty children|ChildrenExec.nil; A=[].|
|C1|childExecutionMeter:22..25, c.paid>q|Execute refusal, then actual childrenAnswersMeter tail; ChildrenExec.refused. A=R. No FOREST or ordinary invocation for this child.|
|C2|Affordable child|Execute actual FOREST(Some(T),c.sourceForest,q-c.paid), then actual child-list tail; ChildrenExec.returned. A=H+R for either None or Some. Child call record is retained even on failure.|
|C3|runChildrenMeter:171..173 after C0..C2|bestLengthMeter runs each retained check in its written order; result, calls and agreementChecks are the declared projection of finishSource. None/Some best selection creates no new ordinary call.|

Every recursive call used in B2 has b-d<b by its actual positive guard. The offsets k used in linear slot lists are assigned from the actual attempt-list length: the next tail uses k+length(H), including nonlive attempts. They are not guessed from a desired SOURCE trace.

## Rule4, Hard2 and all paid paths

|ID|Actual body and exhaustive discriminator|Existing constructor(s); exact attempt order|
|---|---|---|
|R0|Rule4CallerSource.rule4AnswersSource, empty branches|SourceRule4V3.AnswersExec.nil.|
|R1|Nonempty Rule4 branch, cost>q|Execute actual tail first; then actual rule4StateMeter even on this refusal; AnswersExec.refused with the observed false affordability. A=R. Its cell retains state and result=None.|
|R2|Affordable Rule4 branch|Actual tail, actual state, actual FOREST; AnswersExec.returned with those exact subevaluations. A=R+H. Cells stay in input order, so chronological(cells)=reverse(cells).flatMap(labelCell) is derived from evaluation. Rule4Exec.run encloses them; best/branch construction is closed.|
|H0|hard2CompleteSource:124..126: evaluate hard2FrontMeter|runHard2Meter None -> RouteExec.other(refused) and RouteLedger.refused; direct result -> other(direct) and RouteLedger.direct. A=[]. No ordinary call occurs in the graph/classifier/partition/all/filter tests.|
|H1|Disjoint graph: failed all-good, good-filter length=2|Execute the actual Rule5 dispatch D5 below; whole RouteExec.admitted and RouteLedger.admitted, with its actual linear slot list.|
|H2|Disjoint graph: failed all-good, good-filter length!=2|Execute DJ0..DJ2; nonadmitted RouteExec.disjoint, whole RouteExec.other, and RouteLedger.disjoint.|
|H3|Nondisjoint paid graph|Actual paidOuterMeter selects Empty/Good/Hard/Bad. Actual selected body below supplies SourcePaidCaseV3.SelectedExec.empty/good/hard/bad, then PaidExec.run. No additional callback occurs in selection or source wrappers.|
|H4|completeRouteSource:95..97 after H3|Complete actual paid block first, then actual combineSource units U0 below; PaidUnitsExec.run, nonadmitted RouteExec.paid, whole RouteExec.other, corresponding RouteLedger.paid. A=paid+units, even if paid already returned Some. Hard2Exec.run encloses the actual selected route.|
|G0|goodPairLocalSource:12, 2<=q false|SourceGoodPairV3.GoodExec.small; A=[].|
|G1|q sufficient: actual sources, two append computations, target/owned DP; DP None|GoodExec.dpRefused with the actual option equality; A=[]. All preceding retained traversals remain.|
|G2|DP Some(H), actual third append/owned/score exceeds q-2|GoodExec.scoreRefused; A=[].|
|G3|Score affordable|Actual residual target/owned and one actual FOREST at q-2-score; GoodExec.returned with that subevaluation. A=H. checked/reconstruction adds no ordinary call.|
|O0|fullOutputsSource:31, empty output list|SourceFullOutputsV3.OutputsExec.nil.|
|O1|Nonempty full-output list, head unaffordable|Execute actual tail first; OutputsExec.refused. A=R.|
|O2|Affordable full output|Actual tail, sourceForest, actual FOREST, checked and choose; OutputsExec.returned. A=R+H. OutputIndex is the input ordinal, including equal outputs. Actual generated output list then gives HardPaidExec.run.|
|BB0|badPairLocalSource actual restriction guard true/false|SourceBadPairV3.LocalExec.agrees or grouped with that exact guard. True executes the actual local BothBad path with its documented swapped planning roots; false executes grouped with original roots. Neither branch is silently skipped.|
|BB1|bothBadLocalPairLocalSource planning|Actual descendants and plan; SourceBothBadPairV3.PairExec.run on that actual entries list. No callback in planning.|
|BB2|bothBadExecuteLocalSource, empty/nonempty entries|SourceBothBadFoldV3.EntriesExec.nil/cons. Cons executes actual dispatch first, then the entire tail, then checked/choose. A=H+R, even if the head was None or already successful.|
|BB3|bothBadDispatchLocalSource e.mode=ordinary/full/retained|SourceBothBadDispatchV3.DispatchExec.ordinary with actual LocalExec; full with actual FOREST(Some(T),sourceForest,e.budget); retained with actual localTarget/sourceForest/owned FOREST followed by retained reconstruction. These three constructors exhaust Entry.mode; each A is exactly its selected child A.|
|L0|ordinaryLocalSource preparation None/Some(js)|SourceOrdinaryLocalV3.LocalExec.refused/prepared. Some uses actual retained scheduler L1. Final flatten and ordinaryQueriesMeter restrictions create retained call data but perform no callback.|
|L1|scheduleSourceMeter unaffordable/affordable|SourceRetainedSchedulerV3.Schedule.refused/run. Affordable uses actual allocated budget, L2, acceptance; no extra callback in post-charge (omitted accounting).|
|L2|runSourceMeter empty/resolved/hard|SourceRetainedSchedulerV3.Run.nil/resolved/failed/succeeded. Resolved executes tail only; hard executes actual Maf adapter L3. Adapter None stops; Some executes tail. A=[],R,H,or H+R respectively.|
|L3|mafRecursiveMeter restrictions missing/both found|SourceMafCallbackV3.MafExec.missing/returned. Both restrictions run eagerly. Found executes exactly one actual FOREST(Some(t'),[s'],b); A is its list. Missing has A=[]. No callback is made by later ordinaryQueriesMeter data reconstruction.|
|DJ0|disjointRunSource:48..53|Actual singleton constructions, actual unit child list, actual partition, actual disjoint query. SourceDisjointRunV3.DisjointExec.run with those children/query graphs. A=children+query, irrespective of their answers.|
|DJ1|disjointQueryLocalSource parts.length-1>q|SourceDisjointQueryV3.QueryExec.refused; A=[].|
|DJ2|Affordable disjoint query|Actual LocalExec L0 and checked; QueryExec.returned. No additional ordinary call in checking.|
|U0|combineSource:34..38|Actual unitChildren list, C0..C3, unitCalls construction, choose; SourceUnitCombineV3.CombineExec.run. A=unit-child attempts. unitCalls recomputes its declared child/call data, with no callback. Stored calls are units++paid although H4 executes paid first.|

The raw auxiliary disjointExecution has a different evaluation order and is used only for returned values/stored queries. No raw-helper chronology enters DJ0. R1/R2 and O1/O2 construct cells in input order while executing their tails first; their chronological ledger formula follows from these rows, rather than being assumed from a permutation theorem.

## Grouped literal scheduling and Rule5

|ID|Actual body and exhaustive discriminator|Existing constructor(s); exact attempt order|
|---|---|---|
|GR0|groupPairLocalSource actual descendants/output generation|SourceGroupPairV3.PairExec.run on that actual output list; final sourceBest and groupCalls are closed.|
|GR1|groupEvaluateLocalSource empty/nonempty|SourceGroupEvaluationV3.EvaluationExec.nil/cons. Cons executes actual output, groupOutputAnswer, then tail. A=H+R; the output tag is retained.|
|GR2|groupRunOutputLocalSource output unaffordable; jobs builder None; jobs Some|SourceGroupOutputV3.OutputExec.unaffordable/refused/scheduled. Some uses actual remaining budget and literal schedule GR3. A=[] for the first two and child A for scheduled.|
|GR3|literalScheduleSource actual affordability|SourceGroupLiteralV3.Schedule.refused/run; actual known/pending, allocated, schedule and answer-cost guard. The retained nested receipt answers/calls/visits and queries are preserved.|
|GR4|literalRunSource empty/resolved/hard|SourceGroupLiteralV3.Run.nil/resolved/failed/succeeded. Hard first evaluates the actual group callback GR5; None stops with H, Some continues with H+R. Resolved uses R. No parent cutoff is applied before the group adapter: the adapter really runs and its nested FOREST alone reaches PAID.|
|GR5|groupCallbackMeter:48..52|SourceGroupCallbackV3.CallbackExec.run on its actual FOREST(p.target,p.sources,b). AdditionalCost after Some is closed; A is the forest list.|
|D5|dispatchSource finalMeter None/Some(z)|SourceRule5DispatchV3.DispatchExec.refused/selected. None A=[]; Some executes the actual selected case D6. Rule5 answer projection changes only the tag/option.|
|D6|runSelectedSource, all five tags|SourceRule5SelectedV3.SelectedExec.prefixArm/firstArm/thirdArm/commonArm/paidArm, chosen by the actual FinalSelection. No missing branch: the first three use D7, remaining-one uses D8, remaining-second uses D12.|
|D7|selectedArmSource / selectedChildrenMeter|SourceRule5SelectedArmV3.ArmExec.run on the actual selected child list, then C0..C3. Prefix, first and third retain their distinct lists and branch data. A is the children list's A.|
|D8|commonSetupMeter None/Some(d)|SourceRule5CommonV3.CommonExec.refused/built. The full actual setup guard/constructor handling is proved separately in DYNAMIC-CONSTRUCTOR-PREMISES-v1. Some runs D9; setup itself has no ordinary callback.|
|D9|guardedMeter pretest .found(Some(p)) or any other case|SourceRule5CommonV3.GuardedExec.found/refused. Other cases are .refused,.rejected,.found(None), all with A=[]. Found builds its actual cut forest then D10.|
|D10|withOutsideMeter outside reply None/Some(FN)|SourceRule5CommonV3.OutsideExec.refused/paid. Outside reply is a closed finite reconstruction. Some runs D11; None makes no ordinary call.|
|D11|runPaidMeter actual paidJobs and jobsAnswers|SourceRule5CommonV3.PaidExec.run on actual JobsExec. q=0 produces the empty list; q>0 produces the exact two q-1 jobs. JobsExec.nil/cons uses D3 head then tail EVEN after None. Actual reconstruction runs after both and has no ordinary call.|
|D12|solveSelectedMeter actual paidSelectedMeter None/Some(R)|SourceRule5PaidSelectionV3.SolvedExec.refused/built. Preparation repeats its literal final selection and builder search; all such tests/diagnostics execute. Some uses actual BestExec.run and AnswersExec.run, then D13..D15; None makes no ordinary call.|
|D13|requestsMeter, requestListMeter empty/cons, requestForMeter unaffordable/affordable|Actual literalPlan/guardedPlan and list traversal run completely. An unaffordable branch contributes no request and no callback; an affordable branch computes current/opposite/sourceForest/residual and adds its exact PaidRequest. These are closed structural constructors preceding AnswersExec.run. No positivity or uniqueness is assumed.|
|D14|answerListMeter empty/cons|SourceRule5PaidRequestV3.AnswerListExec.nil/cons with actual RequestExec.run. Cons executes actual requestAnswer/current first, then whole tail even on None; A=H+R. BestLength/accepted checks after the list introduce no callback.|
|D15|currentQueryMeter pretest .refused/.found/.rejected|SourceRule5CurrentV3.CurrentExec.malformed/found; rejected r<=1 -> low; rejected r>1 -> hard with that actual one FOREST. Found affordability may return Some/None without FOREST. Only hard has nonempty possible A. Its ordinaryCalls/frontier replay is projected analysis; no extra runtime invocation is attributed to it.|

## Exhaustive no-ordinary and excluded transitions

|ID|Finite body family / exact bindings|Reason its transitions add no local ordinary invocation|
|---|---|---|
|Z0|ELOuter/ELPretest/ELCherry/ELEarly and ELRule4 guards/raw selection|Their supplied predicates use only tree/list data, candidate/choice construction and the typed guard tests proved separately. All four Early selections remain eager; BestMeasured/ChoiceMeasured checks, sizes and comparisons remain allocated. No ordinary closure is called or stored as a subsequently hidden callback.|
|Z1|GenericForest proper/agrees/accepted/checked; jobs/componentPair/overlap/replace/raw|Except the explicitly enumerated disjointAttempt adapter and recursive FOREST calls, these traverse finite trees/lists, restrictions, agreements and source partitions. The two plain raw generators use only the fixed colorLabel tree predicate. Their structural/budget recursion cannot invoke QUERY.|
|Z2|Plain CoreProgram generate/fromTree/run/step/attempt/choose/erase/normalize/groups/mixedCherry; charged Hard2/RW generation|Tree/color/partition/receipt transformations and finite generator recursion. The color closures are the explicit cheap/marked/tree predicates, with no ordinary solver. All output/refusal/visit/childAttempts/pruned/color data remain. Projection v2 changes only its two exact coloring counters.|
|Z3|sourceForest, localTarget, owned, descendants, additionalCost, AllGoodDP.LocalWork.meterRun; checked/choose/reconstruction|The displayed inputs are finite data and fixed agreement/ownership predicates. No ordinary callback occurs inside these families. Every eager duplication in the literal body is still performed; no memoization is used.|
|Z4|BothBad planning, groupProblems/groupPrepare, ordinaryPrepare, all job pretests|Finite preparations with malformed/found/rejected and list-tail cases. groupPrepare's tail runs even if its head failed; ForestDefs.jobs retains its own bind short circuit. These different flows are retained; both have zero ordinary calls.|
|Z5|Classifier/finalMeter and prefix/boundary selection|The CheckReceipt.calls describe finite actual test requests, not ordinary queries. Fixed all/any/options/find closures execute their written tree predicates and build diagnostics. Every constructor tag/refusal and traversal is retained.|
|Z6|paidSelectedMeter, rowsMeter, secondBuilderMeter, buildOneMeter, findBuilderMeter|Actual repeated final selection, rows, subtree/core/leaf-address tests and seventeen LiteralChecks. Failed row continues; first successful row stops. Full tested LiteralProps and typed geometry construction are proved separately. No ordinary callback is in these closures.|
|Z7|setupMeter, guardedPlan/literalPlan/requestFor/requestList, outsideReply/reconstruct, originalAccepted|Closed finite guard/data computations. Setup and geometry proof fields follow from actual tests, with no runtime proof input. Request-list refusals remove only requests; they do not delete a reached value-producing callback.|
|Z8|List/option/tuple/map/filterMap/flatMap/append/find/best, tree equality/restriction/label/path/color/hull primitives, scheduler known/pending/allocated/answerCost, ordinaryQueries/unitCalls/groupCalls|Use only their particular fixed closures already listed. A closed closure contributes no call. A closure calling FOREST/PAID contributes exactly the calls at its census row, once per actual application. List tail/eager/short-circuit behavior remains literal. Data reconstruction of a call list never invokes the recorded call.|
|X0|Precisely the PROJECTION-v1 work-only table and ACCOUNTING-READ-SITES, plus amendment v2's two fields|C/debit/forestWork/nonrecursiveBill, childForestDebit, callsForestDebit, concreteResiduals work probes, W/w/fee/classFee/literalFee and scalar accounting-only subexpressions have no runtime evaluation. currentQueryMeter's one ordinaryCalls/frontier producer and its propagation-only fields are omitted. postChargeMeter is omitted only in its stated accounting context. These exclusions do not cover any value-producing let or retained diagnostic.|

The zero-call claim is closed under the exact finite primitive call graph: the bodies in Z0..Z8 recurse only within these finite structural/data families or through the explicitly listed callback applications. No argument identifies a function as zero-call merely because its name sounds administrative. In particular the generic higher-order functions are classified by their actual bound closure; callbacks at F3/F5, C2, R2, G3, O2, BB3, L3, GR5, D3 and D15 are explicitly kept. Every source occurrence of QUERY's direct recursion, actual/ordinary/cb/f application or FOREST recursion in the runtime portion is therefore D0..D3, P0 or a forwarding application in this census. ActualCaller/ConcreteFees/admittedRouteSource only bind and forward these same closures. The appendix's raw FastSolve body is a mathematical comparison definition, not a second procedure executed beside QUERY; OWScan's query application is outside the body of a fixed QUERY and outside this obligation.
