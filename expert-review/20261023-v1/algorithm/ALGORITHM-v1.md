# Ordinary rooted MAF: mathematical implementation v1

This is the computation specification for TARGET-v3. It consists of this execution entry, the finite procedure index, the literal typed procedure appendix, the constructor data/type projections, and the operational projection below. It does not claim the cost theorem or its independent acceptance. The old numeric candidates are separate optional artifacts and retain their fault ports.

`C` and the functions that calculate source-counter debits are mathematical analysis, never inputs, returned machine words, answer procedures, or executed callback replays. The ordinary pair is supplied by the exact packed natural word U(T,S), plus the budget word q, using the paid decoder specified in REPRESENTATION-AND-OPERATIONS. `QUERY(q,T,S)` uses that budget. `OPTIMIZE(T,S)` computes its budgets internally; any supplied q word is not a search bound. There is no supplied optimum, properness promise, answer, fee, width, trace, callback, or mode.

## Procedure index and complete execution graph

Names in the table designate literal bodies in PROCEDURES-v1.md and SOURCE-INDEX-v1.tsv. The latter records every included declaration's exact source view, original lines and source digest. `R[f]` below is the one fixed runtime procedure obtained by the explicitly enumerated field projection in PROJECTION-v1.md. It is notation for that finite procedure's body, not a runtime evaluator or a supplied function. Qualified aliases are resolved by the original source module and its namespace/import context in SOURCE-BINDING-v1.json. Higher-order list helpers below receive only the displayed finite predicates; the only recursive ordinary callback is `PAID(parentBudget,...)` defined here.

|Entry/family|Literal computation and callees|
|---|---|
|QUERY|ELOuter.meterFront; CompleteOrdinaryStep.completeBranchSource with recursive calls bound below|
|FRONT|ELPretest.meterPretest, meterCandidates, meterBest, meterCandidate, meterForest, meterAgreement; ELEarly.meterEarly|
|EARLY|ELCherry.meterSelect in both orientations; ELEarly.meterRule4Select in both orientations, all eager|
|SELECT|ELCherry.meterCherries/meterCherryCandidates; three distinct ELPrimitives.meterFind traversals|
|RULE4_SELECT|ELRule4Guards.meterRule4Priority; ELRule4Raw.meterRawChoices/meterRawAB/meterRawAC/meterRawR; released meterFirstChoice projection and meterLocalGuard|
|COMMON|CommonBranchWork.commonBranchMeter; CommonConstructionWork.commonPairMeter/contractMeter/expandCommonMeter and their literal helpers|
|ONE/HIGH|SelectedRestriction.pendantChildMeter; PrefixChildrenWork.singletonChildMeter; OrdinaryChildrenSource.branchesMeter; ChildrenExecutionWork.childrenAnswersMeter/childExecutionMeter/bestLengthMeter|
|RULE4_RUN|Rule4CallerSource.rule4BranchesMeter/rule4StateMeter/rule4AnswersSource/rule4Source; FOREST for every affordable branch|
|HARD2|Hard2RouteSource.hard2FrontMeter; Hard2GraphSource.runHard2Meter; partition/all/filter and CompleteNamedSources.completeRouteSource|
|RULE5_ADMITTED|ActualCaller.rule5AnswerSource; ConcreteFees.source; Rule5SelectedSource.dispatchSource/runSelectedSource|
|RULE5 selector|FinalClassifierWork.finalMeter and finite PrefixScans, LocalSelector, BoundarySelector, CheckFamilies, ClassifierRequestMeter and CheckAssembly bodies in the appendix|
|RULE5 prefix/first/third|SelectedAgreementBinding.selectedArmSource; SelectedChildrenWork.selectedChildrenMeter; ONE/HIGH child engine|
|RULE5 remaining-one|CommonPaidSource.commonSource/runPaidMeter; CommonLocalBinding, CommonGuardedSource, CommonOutsideSource bodies|
|RULE5 remaining-second|PaidBestSource.paidSelectedSource/solveSelectedMeter/paidSelectedMeter; PaidBuilderOuter buildOneMeter/findBuilderMeter/secondBuilderMeter; SetupBuilder.setupMeter and SelectorBuilder.ofProps released exact data/guard projections|
|RULE5 literal checks|The seventeen LiteralChecks predicates below, LiteralAtoms.checksMeter, LiteralDecision.literalMeter, LiteralStructural and LiteralAtoms equality/Boolean bodies|
|RULE5 literal schedule|LiteralScheduleReceiptSource.literalScheduleSource/literalRunSource; SchedulerAtoms/SchedulerRun/SchedulerSchedule; actual callback adapters in OrdinarySchedulerSource and GroupedJobsSource|
|DISJOINT_PARENTS|DisjointParentSource.disjointRunSource/disjointQueryLocalSource; partition, good-component filtering, source forest and FOREST; no analytical disjointQuerySource debit replay|
|HARD2 paid selection|PaidOuterSource.paidOuterMeter; CompleteNamedSources.selectedPaidSource: empty/good/hard/bad cases below|
|GOOD_PAIR|GoodPairSource.goodPairLocalSource; AllGoodDP.LocalWork.meterRun; owned/local target/additionalCost; at most its actual residual FOREST query|
|HARD_PAID|Hard2OutputGenerationSource.actualOutputsMeter/edgeOutputsMeter/kindOutputsMeter/hardPaidSource; Hard2GeneratorSource; Hard2FullOutputSource.fullOutputsSource/checkedMeter/chooseMeter|
|BAD_PAIR|BadPairSource.badPairLocalSource; restriction-agrees test chooses BothBadLocalExecutionSource or GroupedExecutionSource, preserving that test's order|
|BOTH_BAD|BothBadPlanSource.bothBadPlanMeter and finite planner atoms; BothBadLocalExecutionSource.bothBadExecuteLocalSource/bothBadDispatchLocalSource/retainedReconstructionMeter|
|GROUPED_PAIR|GroupedExecutionSource.groupPairLocalSource/groupEvaluateLocalSource/groupOutputAnswerMeter/groupCalls; GroupedJobsSource prepare/problems/jobs/callback/output procedures; SourceBestMeter.sourceBestMeter; MergeEnumeration/MergeOperations/CheckedMerge|
|COMBINE|UnitCombineSource.combineSource/unitChildrenMeter/unitCallsMeter; run the unit child engine even after paid computation; Hard2FullOutputSource.chooseMeter|
|FOREST|ForestProgram.solve/branches/checked/disjointSolve; ForestDefs proper/agrees/overlap/raw/replace/jobs/disjointAttempt, GroupState, OverlapDefs, QueryCaller|
|FOREST raw generation|Plain CoreProgram.generate/fromTree/run/step/attempt/choose/erase/normalize/groups/mixedCherry; Bridge.colorLabel. This is distinct from the charged recovery generator|
|FOREST disjoint scheduler|QueryCaller.schedule and its literal run; knownCost, pending, allocated, answerCost; early refusal and exact hard-job callbacks below|
|OPTIMIZE|OWScan.meterPreflight/meterScan; OptimizerSourceBodies.sourceFinishMeter; one RECOVER on success|
|RECOVER|OWRecovery.meterInputCheck; RWFinal.meterRecover/meterColor; RWInitial.meterGenerate/meterInitial/meterBuild; RWRun/RWLocal/RWChoose/RWTree and complete colored receipts|
|Finite primitives|Lists, options, products, equality, paths, leaves, subtree, rooted/minimal hulls, pendant components, restrictions, agreement, color/DP, relabel/marked/partition builders: literal definitions in the appendix and elementary implementations below|

All named support bodies are part of the implementation appendix. A family name in this table does not introduce an additional atomic operation. No routine is licensed to fetch an answer from the functional theorem. The source binding records the distinct bodies with similar names, including plain versus charged generate, eager versus short-circuit all/any, and grouped versus ordinary length.

## Entry and recursive ordinary query

Use natural subtraction truncated at zero, written `sub`. `None` and `Some` are options, not exceptions. Every written constructor allocates its actual retained record/list cells. Evaluations separated by semicolons happen left to right unless a routine explicitly says tail first. Boolean and/or short-circuit their unevaluated right expression; separate preceding lets are already evaluated and stay eager. Functions passed as fixed predicates are finite lexical closures containing their displayed captured values. Creating their environment and list cells is real work, even if a later short-circuit does not invoke them.

```text
QUERY(q,T,S):
    front := R[ELOuter.meterFront](q,T,S)
    case front of
      Stop(answer): return answer
      Selected(e): return BRANCH(q,T,S,e)

PAID(parentBudget,U,V,r):
    if r < parentBudget: return QUERY(r,U,V)
    return None

BRANCH(q,T,S,e):
    case e of
      Common(reverse,c):
        p := R[CommonConstructionWork.commonPairMeter](T,S,reverse,c)
        a := R[meterLeaves](p.first); b := R[meterLeaves](T)
        if length(a) < length(b):
            answer := QUERY(q,p.first,p.second)
            if answer=None: return None
            return Some(R[expandCommonMeter](T,S,reverse,c,answer.payload))
        return None
      One(reverse,c):
        (U,V) := if reverse then (S,T) else (T,S)
        child := R[pendantChildMeter](V,c.a,c.b)
        return RUN_CHILDREN(PAID(q),U,V,q,[child])
      High(reverse,c):
        (U,V) := if reverse then (S,T) else (T,S)
        x := R[singletonChildMeter](V,c.a)
        y := R[singletonChildMeter](V,c.b)
        p := R[pendantChildMeter](V,c.a,c.b)
        return RUN_CHILDREN(PAID(q),U,V,q,[x,y,p])
      Rule4Forward(choice): return RULE4_RUN(PAID(q),choice,q)
      Rule4Reverse(choice): return RULE4_RUN(PAID(q),choice,q)
      Hard2(c,d): return HARD2(PAID(q),T,S,c,q)  // d is selected and retained; dispatcher uses c
      Refused: return None
```

Only COMMON calls the same-budget ordinary query, after the actual strict leaf-count comparison. All other ordinary callbacks use PAID with the current parent budget. Forest recursion additionally decreases its own budget on every overlap branch. These are operational tests, not correctness promises. Recursive calls are implemented with paid stack records; no host recursion or cost oracle is assumed.

```text
FRONT(q,T,S):
    p := OrdinaryProper(T,S)
    if not p: return Stop(None)
    d := PRETEST(T,S)                         // repeats OrdinaryProper
    case d of
      Refused: return Stop(None)
      Found(c):
        F := ForestOfCut(S,c)                 // before affordability test
        return Stop(if CutCost(c)<=q then Some(F) else None)
      Rejected: return Selected(EARLY(T,S))

PRETEST(T,S):
    if not OrdinaryProper(T,S): return Refused
    edges := Edges(S)
    candidates := None :: map(Some,edges)
    best := BEST_CUT(T,S,candidates)
    return if best.value=None then Rejected else Found(best.value.payload)

BEST_CUT(T,S,[]): return {value:None,checks:[],tailSizes:[],comparisons:[]}
BEST_CUT(T,S,x::xs):
    valid := R[ELPretest.meterAgreement](T,S,ForestOfCut(S,x))
    r := BEST_CUT(T,S,xs)                     // entire tail even when valid
    if not valid:
        return {value:r.value,checks:(x,false)::r.checks,
                tailSizes:length(xs)::r.tailSizes,comparisons:r.comparisons}
    if r.value=None:
        return {value:Some(x),checks:(x,true)::r.checks,
                tailSizes:length(xs)::r.tailSizes,comparisons:r.comparisons}
    y := r.value.payload
    value := if CutCost(x)<=CutCost(y) then Some(x) else Some(y)
    checks := (x,true)::r.checks
    sizes := length(xs)::r.tailSizes
    comparisons := (CutCost(x),CutCost(y))::r.comparisons
    return {value:value,checks:checks,tailSizes:sizes,comparisons:comparisons}

CutCost(None)=0; CutCost(Some(path))=1
ForestOfCut(S,None)=[Leaves(S)]
ForestOfCut(S,Some(v)):
    a := SubtreeLabels(S,v)
    b := filter(x => not Contains(x,SubtreeLabels(S,v)),Leaves(S))
    return [a,b]                             // recompute labels inside predicate
```

The pretest's ELPretest.meterAgreement eagerly computes leaves/partition on T, leaves/partition on S, all restriction-agrees checks, pairwise hull disjointness on T and on S before combining the Booleans. Plain RMAF.agreement is a separate short-circuit body in AGREEMENT-DATA-v1.json. ChildrenExecutionWork.acceptedMeter calls that plain body; Hard2 checkedMeter calls its own GeneralAgreementWork.agreementMeter body. The explicit source bindings preserve those different evaluation orders. None is an agreement oracle.

```text
EARLY(T,S):
    f := SELECT(T,S); r := SELECT(S,T)
    a := RULE4_SELECT(T,S); b := RULE4_SELECT(S,T) // all four before matching
    return first matching case in this exact order:
      f.common => Common(false,f.c); r.common => Common(true,r.c)
      f.one => One(false,f.c);       r.one => One(true,r.c)
      f.high => High(false,f.c);     r.high => High(true,r.c)
      f.hard2 and r.hard2 => if a=Some(s) then Rule4Forward(s)
                           else if b=Some(s) then Rule4Reverse(s)
                           else Hard2(f.c,r.c)
      otherwise => Refused

SELECT(T,S):
    cs := map((p,a,b) => Candidate(p,a,b,Pendant(S,a,b)),Cherries(T))
    common := find(c => isEmpty(c.originalCuts),cs)
    one := find(c => length(c.originalCuts)=1,cs)
    high := find(c => 3<=length(c.originalCuts),cs)
    if common=Some(c): return Some(Common,c)
    if one=Some(c): return Some(One,c)
    if high=Some(c): return Some(High,c)
    return mapOption(c => (Hard2,c),headOption(cs))

RULE4_SELECT(T,S):
    proper := OrdinaryProper(T,S)
    noCommon := AllNoCommon(T,S)
    noOneF := AllNoOne(T,S); noOneR := AllNoOne(S,T) // eager
    if not(proper and noCommon and noOneF and noOneR): return None
    raw := RawChoices(T,S)                    // exact ordered flatMaps in appendix
    measured := FIRST_CHOICE(T,S,raw)
    return measured.value

FIRST_CHOICE(T,S,[]): return {value:None,checks:[]}
FIRST_CHOICE(T,S,x::xs):
    guard := LocalGuard(T,S,x)                // all eight computations eager
    if guard: return {value:Some(x),checks:[(x,true)]}
    r := FIRST_CHOICE(T,S,xs)
    return {value:r.value,checks:(x,false)::r.checks}
```

RawChoices, its repeated Pendant calls and every equality/length/guard are literal bodies, not a search oracle. Rule4.Choice retains its raw data. Its Priority and LocalGuard are full logical types in the released data/type appendix; neither a proof token nor an admission Boolean is an extra input.

## Children, Rule4 and all Hard2 routes

```text
CHILD_EXEC(cb,T,q,c):
    if c.paid<=q:
        b := sub(q,c.paid)
        answer := FOREST(cb,Some(T),c.sourceForest,b)
        return {value:answer,calls:[(c,b)]}
    return {value:None,calls:[]}
CHILD_ANSWERS(cb,T,q,[]): return {value:[],calls:[]}
CHILD_ANSWERS(cb,T,q,c::cs):
    a := CHILD_EXEC(cb,T,q,c)
    tail := CHILD_ANSWERS(cb,T,q,cs)
    return {value:(if a.value=None then tail.value else a.value.payload::tail.value),
            calls:append(a.calls,tail.calls)}

RUN_CHILDREN(cb,T,S,q,cs):
    r := CHILD_ANSWERS(cb,T,q,cs)
    b := BEST_LENGTH(F => RMAF.agreement(T,S,F) and (sub(length(F),1)<=q),r.value)
    receipt := {value:b,calls:r.calls,agreementChecks:r.value}
    return receipt.value                    // discarded receipt stays allocated

BEST_LENGTH(check,[]): return None
BEST_LENGTH(check,F::fs):
    good := check(F); r := BEST_LENGTH(check,fs) // eager check then entire tail
    if not good: return r
    if r=None or length(F)<=length(r.payload): return Some(F)
    return r

RULE4_RUN(cb,choice,q):
    bs := R[rule4BranchesMeter](choice)
    answers := RULE4_ANSWERS(cb,q,bs)
    return BEST_LENGTH(F => true,answers)
RULE4_ANSWERS(cb,q,[]): return []
RULE4_ANSWERS(cb,q,b::bs):
    r := RULE4_ANSWERS(cb,q,bs)               // tail first, preserve duplicates
    state := R[rule4StateMeter](b)            // also when b.cost>q
    if length(b.cuts)<=q:
        a := FOREST(cb,Some(b.target),state,sub(q,length(b.cuts)))
        return append(optionToList(a),r)
    return r

HARD2(cb,T,S,c,q):
    graph := R[runHard2Meter](T,S,c)
    if graph=None: return None
    if graph.payload=Disjoint:
        p := R[partitionMeter](S,c.a,c.b)
        goodAll := eagerAll(B => R[TreeCheckMeters.meterRestrictionAgrees](T,S,B),p)
        if goodAll: return if sub(length(p),1)<=q then Some(p) else None
        good := eagerFilter(B => R[TreeCheckMeters.meterRestrictionAgrees](T,S,B),p)
        if length(good)=2: return RULE5(cb,T,S,c.a,c.b,q)
        return R[DisjointParentSource.disjointRunSource](cb,T,S,c.a,c.b,q)
    out := graph.payload
    route := R[PaidOuterSource.paidOuterMeter](T,S,c,out)
    case route of
      Empty: paid := {answer:None,calls:[]}
      Good(X,Y,Z): paid := R[GoodPairSource.goodPairLocalSource](cb,T,S,X,Y,Z,q)
      Hard: paid := R[Hard2OutputGenerationSource.hardPaidSource](cb,T,S,q,c,out)
      Bad(X,Y,Z,edge): paid := R[BadPairSource.badPairLocalSource](cb,T,S,X,Y,Z,edge,q)
    return R[UnitCombineSource.combineSource](cb,T,S,c.a,c.b,q,paid).answer
```

`combineSource` runs its unit child construction and child engine even if a paid answer is already present, constructs its calls list and performs its literal tie-breaking choice. `BadPairSource` tests RestrictionAgrees(S,T,C) first: true selects bothBadLocalPairLocalSource with swapped roots; false selects groupPairLocalSource with original roots and constructs groupCalls from its actual queries. GoodPair does its actual three-block source forest, two separate A++B constructions, target/owned DP, repeated scoring source construction, additionalCost comparison, residual budget, residual forest call and final checked reconstruction. None of these names denotes a missing body: their complete branch code and all helper code are in the appendix.

BothBad's finite Entry.mode cases are ordinary, full, and retained. Ordinary uses ordinaryLocalSource; full builds the source forest and calls FOREST on Some(T); retained builds the residual local target/source forest/owned sources, calls FOREST at e.budget, then retainedReconstructionMeter with the stored known/completed fields. bothBadExecuteLocalSource executes current dispatch, then the entire tail, then checks current answer and chooses between checked current and tail. Grouped execution keeps every output, candidate, query, ordered merge, owner test and refusal, including duplicates. Source trace-list concatenation is retained in the specified stored order; it is not assumed to be chronological execution.

## Every Rule5 caller

```text
RULE5(cb,T,S,a,b,q):
    result := R[ConcreteFees.source](cb,T,S,a,b,q)
    return if result=Answered(answer) then answer else None

RULE5_DISPATCH(cb,T,S,a,b,q):
    z := R[finalMeter](T,S,a,b)
    if z=None: return SelectorRefused
    case z.payload of
      Prefix(s): return Answered(R[selectedArmSource](cb,T,S,a,b,q,Prefix(s)))
      Remaining(d,First(u,v)):
        return Answered(R[selectedArmSource](cb,T,S,a,b,q,Remaining(d,First(u,v))))
      Remaining(d,Third(u,v)):
        return Answered(R[selectedArmSource](cb,T,S,a,b,q,Remaining(d,Third(u,v))))
      Remaining(d,One(x)):
        return Answered(R[commonSource](cb,T,S,a,b,d,q))
      Remaining(d,Second(u,v)):
        r := R[paidSelectedSource](cb,T,S,a,b,q)
        return if r=BuilderRefused then PaidBuilderRefused else Answered(r.answer)
```

`ConcreteFees.source` is the fixed dispatchSource specialization, not an external classifier/fee. Its classFee/literalFee analysis arguments are removed. finalMeter retains all classification tests and exact priority/refusal. selectedArmSource constructs the declared selected children then uses RUN_CHILDREN. commonSource retains its actual setup, same-budget/paid-call checks, common reconstruction and outside handling. paidSelectedSource retains final selection, both literal builder searches, setupMeter's complete guards and refusals, ofProps' exact data selections, the seventeen literal predicates, literal schedule, actual answers, best/checked reconstruction. The full bodies are indexed individually, so the second boundary case is not hidden behind an unspecified Rule5 macro.

LiteralChecks' outer fixed list has these predicates, in order, with captured environment `(T,S,a,b,d,u,v,R,C,qa,ub)`. All list/closure cells are constructed before checksMeter short-circuits: properPair; atTree(S,R.w,bottom(...)); cherryExists(T,R.a,R.b); cutsTwo(S,R.a,R.b); labels(T,C,R.X,d.c); containsTree(C,R.b); not containsTree(C,d.c); leafAt(T,qa,R.a); leafAt(T,ub,R.b); leafAt(T,u,d.c); short-circuit incidentEq(T,R.X,u,v) OR incidentEq(T,R.X,v,u); tailMem(T,R.X,v); tailMem(T,R.X,u); not minimalMem(T,R.X,v); not minimalMem(T,R.X,u); boundaryEq(S,R.X,d.badArc); `(R.a=a and R.b=b) or (R.a=b and R.b=a)`. The nested OR's second closure is allocated but invoked only on first-arm false. The appendix gives the exact non-abbreviated bottom fields and every predicate body. The full EndpointOrder type is retained separately from these four natural comparisons.

The two proof-bearing constructor projections have these explicit runtime bodies. No test is replaced by a proof input:

```text
SETUP(T,S,X,Y,p):
    if not Nodup(Leaves(T)): return None
    if not Nodup(Leaves(S)): return None
    if not PartitionCheck(Leaves(T),[X,Y]): return None
    if not PartitionCheck(Leaves(S),[X,Y]): return None
    if p=[]: return None
    u:=Subtree(S,p); if u=None: return None
    if not Perm(Leaves(u.payload),X): return None
    boundary:=Incident(T,X)
    if boundary is not a one-element list: return None
    x:=headD(X,0); y:=headD(Y,0)
    L:=append(Leaves(T),Leaves(S))
    rho:=LabelMax(L)+1; gamma:=LabelMax(L)+2 // two actual max traversals
    tx:=Restrict(X,T); sx:=Restrict(X,S); ty:=Restrict(Y,T); sy:=Restrict(Y,S)
    mxT:=Marked(T,X,y,rho); mxS:=Marked(S,X,y,rho)
    myT:=Marked(T,Y,x,gamma); myS:=Marked(S,Y,x,gamma) // all eight eager
    if any of these eight options is None: return None
    return Some(Setup(T,S,tx.payload,sx.payload,ty.payload,sy.payload,
                      mxT.payload,mxS.payload,myT.payload,myS.payload,X,Y,x,y,rho,gamma))

LITERAL_GEOMETRY_FROM_TESTED_DATA(T,S,d,u,v,R,C,qa,ub):
    // Called by buildOneMeter only after its actual subtree-core and LiteralChecks tests.
    return LiteralGeometry(X=R.X,C=C,w=R.w,r=v,qa=qa,ub=ub,uc=u,
                           sa=R.sa,sc=R.sc,sb=R.sb,a=R.a,b=R.b,c=d.c)
```

Incident,Marked,LabelMax,Restrict,PartitionCheck,Nodup and Perm here are the indexed finite bodies/elementary list routines, not mathematical predicates available at unit cost. The complete Setup/LiteralGeometry Prop types, exact caller premise tests, field order and source/object identities remain in CONSTRUCTOR-DATA-v1.json. `bottom(...)` above expands to `bottom(R.sa,R.sc,R.sb,R.a,R.b,d.c,R.X)` in the atTree predicate; its source orientation/tree construction is an explicit appendix body.

## Forest solver, scheduling and raw generation

```text
FOREST(cb,Toption,ss,q):
    if not R[GenericForest.proper](Toption,ss): return None
    partition := map(Leaves,ss)
    if R[GenericForest.agrees](Toption,ss,partition): return Some(map(Leaves,ss))
    if Toption=None: return None
    t := Toption.payload
    if ss=[s]: return bind(cb(t,s,q),F => CHECKED(Toption,ss,q,F))
    h := R[overlap](t,ss)
    if h=None:
        receipt := R[disjointAttempt](t,ss,cb,q)
        if receipt=None or receipt.payload.answers=None: return None
        F := flatMap(pair => pair.second,receipt.payload.answers.payload)
        return CHECKED(Some(t),ss,q,F)
    left := map(o => (h.left,o),R[raw](t,ss,h.left,h.vertex,q))
    right := map(o => (h.right,o),R[raw](t,ss,h.right,h.vertex,q))
    answers := []
    for (index,o) in append(left,right), from head to tail:
        d := length(o.sourceCuts)
        if 1<=d and d<=q:
            a := FOREST(cb,Toption,R[replace](ss,index,o.partition),sub(q,d))
            if a=Some(F): append one F cell to the accumulated answer sequence
    return BEST_LENGTH(F => R[accepted](Toption,ss,q,F),answers)
CHECKED(Toption,ss,q,F):
    return if R[accepted](Toption,ss,q,F) then Some(F) else None
```

The for-loop means the literal filterMap order with immutable list construction, not constant-time append: keep successful heads in a paid reverse accumulator and reverse it by a paid traversal, or use the appendix's recursive filterMap and paid callframes. This version fixes the latter recursive filterMap implementation to avoid changing evaluation order. The source ss.map leaves occurs twice on the immediate-agreement branch; the two calls are retained, not cached.

QueryCaller has only Resolved(problem,cost,answer) and Hard(problem) jobs. The scheduler computes knownCost as the sum of resolved costs and pending as the number of hard jobs. It refuses before any hard query if `q < knownCost + 2*pending`. Otherwise it separately recomputes its allocated budget using the literal allocated body in the appendix. Its run processes a resolved job by running the tail and then prepending the stored answer. A hard job invokes its fixed callback at that allocated budget, stops immediately on None, or runs the tail and prepends its actual result/call record on success. It retains visits and calls. Final answerCost<=q is checked, and the specified post-charge metadata traversal stays paid whenever its result is a retained diagnostic; pure accounting fields are projected explicitly. Literal/source scheduler variants remain distinct as indexed.

```text
KNOWN_COST([])=0
KNOWN_COST(Resolved(_,c,_)::js)=c+KNOWN_COST(js)
KNOWN_COST(Hard(_)::js)=KNOWN_COST(js)
PENDING([])=0
PENDING(Resolved(_,_,_)::js)=PENDING(js)
PENDING(Hard(_)::js)=1+PENDING(js)
ALLOCATED(q,js)=sub(sub(q,KNOWN_COST(js)),2*sub(PENDING(js),1))
ANSWER_COST(xs)=sum(map(first,xs))
SCHEDULE(f,q,js):
    k:=KNOWN_COST(js); p:=PENDING(js)
    if q<k+2*p: return {answers:None,calls:[],visits:0}
    b:=ALLOCATED(q,js)                       // fresh known/pending traversals
    r:=RUN_JOBS(f,b,js)
    if r.answers=Some(xs) and ANSWER_COST(xs)>q: r.answers:=None
    return the freshly constructed retained receipt r
RUN_JOBS(f,b,[]): return {answers:Some([]),calls:[],visits:0}
RUN_JOBS(f,b,Resolved(_,c,a)::js):
    r:=RUN_JOBS(f,b,js)
    return {answers:mapOption(xs=>(c,a)::xs,r.answers),calls:r.calls,visits:r.visits+1}
RUN_JOBS(f,b,Hard(p)::js):
    a:=f(p,b)                               // finite fixed adapter; no oracle
    if a=None: return {answers:None,calls:[b],visits:1}
    r:=RUN_JOBS(f,b,js)
    return {answers:mapOption(xs=>a.payload::xs,r.answers),calls:b::r.calls,visits:r.visits+1}
```

The receipt update notation constructs a new immutable record; it is not an uncharged array/memory update. The literal scheduler additionally prepends its `(problem,b)` query cells exactly at the printed sites in literalRunSource. Its query ordering, optional answers and visits use that separate complete body.

raw calls plain CoreProgram.generate with the saved target/vertex colorLabel, actual budget, and original selected source tree. Its finite colored-tree routine has every root/duplicate-label/duplicate-cut/whole-source refusal shown in the appendix. Plain erase checks a matching root before recursing; plain attempt tests root/duplicate before erasing; plain choose defers mixedCherry until earlier cases fail. It retains outputs/sourceCuts/partition/refusals/visited/childAttempts/pruned. Recovery's RW family has a separately defined, more eager implementation; no informal same-name substitution is allowed.

## Finite optimizer and one recovery

```text
OPTIMIZE(T,S):
    p := OrdinaryProper(T,S)
    labels := Leaves(T)
    fuel := length(labels)                     // even on malformed input
    if not p: return Execution(Scan(None,[]),None,[])
    search := SCAN(T,S,0,fuel)
    if search.selected=None: return Execution(search,None,[])
    (budget,F) := search.selected.payload
    recovered := RECOVER(S,F)                   // exactly one call
    return Execution(search,recovered,[(F,recovered)])

SCAN(T,S,start,0): return Scan(None,[])
SCAN(T,S,start,fuel+1):
    a := QUERY(start,T,S)
    if a=Some(F): return Scan(Some(start,F),[(start,a)])
    r := SCAN(T,S,start+1,fuel)
    return Scan(r.selected,(start,a)::r.trials)

RECOVER(S,F): return R[RWFinal.meterRecover](S,F)
```

RECOVER executes its actual input check first. On true it traverses F for its length, evaluates RWInitial.meterGenerate with color(F) and `sub(length(F),1)`, then takes outputs.headOption. Generation performs Leaves/Nodup, repeats Leaves/length on success, constructs the colored tree and caps cuts at `min(inputBudget,sub(leafLength,1))`. Color scans blocks in order using Contains and headD0. RWRun normalizes both subtrees, computes groups and color tests, then finishes, attempts one source cut, or evaluates both cut attempts. It combines all output/cut/refusal/visited/attempt/pruned fields in literal order. A refused input does not call the generator. These are complete appendix bodies, not a recovery oracle.

The finite fuel is the actual leaf count, independent of any external q. The completed functional contracts in FUNCTIONAL-CONTRACT-v1.json concern the canonical ordinary input, malformed refusal, minimum component forest, ordered failed trials and exactly one realized recovery. Their theorem types and source/object pins are supplied support. No proof body, cost theorem, novelty claim, numeric-program acceptance or missing source correspondence is inferred from them.
