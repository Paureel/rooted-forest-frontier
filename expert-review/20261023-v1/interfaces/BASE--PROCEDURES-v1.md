# Literal typed procedure appendix

These are the finite pure computational/type bodies, with exact original line labels, that define the procedures in ALGORITHM-v1.md. This is readable typed pattern-matching pseudocode, not a Lean execution requirement. `let` is sequential; pattern branches and higher-order list operations have the evaluation rules stated in the algorithm and representation specification. The declaration's original module/source/line identity resolves namespace abbreviations; CONTEXTS-v1.txt supplies import/open/namespace line metadata without proof bodies.

The original metered notation remains visible so readers can inspect precisely which fields were projected. Apply only the finite operational projection in PROJECTION-v1.md: analysis fields/arguments have no machine slot and their accounting expressions are not executed. Other value-producing lets, guards, candidates and retained diagnostics are executed in the written order. `FastOrdinary.solve` at a runtime recursive position binds QUERY; `cutoff FastOrdinary.solve q` binds PAID(q). Every other ordinary callback parameter is that explicitly passed closure. No source work/debit/counter evaluator is a machine primitive. Original type-only Prop fields are logical obligations; their finite actual tests are retained. Full exact constructor data/guard/type projections are appended separately because their source bodies contain proof values.

The duplicated source references are identities, not calls to an external library. The following sections ARE the helper definitions used by the main pseudocode, including Hard2/Rule5 branches, forest completion, all finite selectors/builders and recovery. The two deliberately excluded unsafe body views and planted fixture are not part of this appendix. LiteralChecks and the two Rule4 selector bodies have their exact data definitions in the main algorithm and released projections instead.


## source-CommonBranchWork-commonBranchMeter.txt

```text
CommonBranchWork.lean:9: def commonBranchMeter (rec : Nat→Tree→Tree→Option (List (List Nat))) (W : OrdinaryWork)
CommonBranchWork.lean:10:  (q : Nat) (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Charged (Option (List (List Nat))) :=
CommonBranchWork.lean:11:  let p:=commonPairMeter T S reverse c
CommonBranchWork.lean:12:  let a:=meterLeaves p.value.1;let b:=meterLeaves T
CommonBranchWork.lean:13:  if a.value.length<b.value.length then
CommonBranchWork.lean:14:   let answer:=rec q p.value.1 p.value.2
CommonBranchWork.lean:15:   match answer with
CommonBranchWork.lean:16:   | none=>⟨none,p.work+a.work+b.work+W p.value.1 p.value.2 q+8⟩
CommonBranchWork.lean:17:   | some F=>let e:=expandCommonMeter T S reverse c F
CommonBranchWork.lean:18:             ⟨some e.value,p.work+a.work+b.work+W p.value.1 p.value.2 q+e.work+8⟩
CommonBranchWork.lean:19:  else ⟨none,p.work+a.work+b.work+4⟩
```

## source-CompleteNamedSources-completeRouteSource_concreteResiduals_hard2CompleteSource.txt

```text
CompleteNamedSources.lean:12: def concreteResiduals (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
CompleteNamedSources.lean:13:  (c : CherryBranching.Candidate) (q : Nat) : OpenHandlerResiduals :=
CompleteNamedSources.lean:14:  ⟨(disjointRunSource actual (fun _ _ _=>0) T S c.a c.b q).work,
CompleteNamedSources.lean:15:   fun route=>match route with
CompleteNamedSources.lean:16:    | .bad X Y Z edge=>(badPairSource actual (fun _ _ _=>0) T S X Y Z edge q).work
CompleteNamedSources.lean:17:    | _=>0⟩

CompleteNamedSources.lean:88: def completeRouteSource (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate)
CompleteNamedSources.lean:89:  (q : Nat) : Hard2Route→Charged (Option (List (List Nat)))
CompleteNamedSources.lean:90:  | .refused=>⟨none,0⟩
CompleteNamedSources.lean:91:  | .direct a=>⟨a,0⟩
CompleteNamedSources.lean:92:  | .admittedRule5=>admittedRouteSource W T S c q
CompleteNamedSources.lean:93:  | .disjointPaid=>disjointRunSource (cutoff FastOrdinary.solve q) W T S c.a c.b q
CompleteNamedSources.lean:94:  | .paid out=>
CompleteNamedSources.lean:95:   let p:=paidCaseCompleteSource (cutoff FastOrdinary.solve q) W T S c q out
CompleteNamedSources.lean:96:   let r:=combineSource (cutoff FastOrdinary.solve q) W T S c.a c.b q p.value
CompleteNamedSources.lean:97:   ⟨r.value.answer,p.work+r.work+2⟩

CompleteNamedSources.lean:122: def hard2CompleteSource (W : GenericForest.FrontierWork.OrdinaryWork) (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) :
CompleteNamedSources.lean:123:  Charged (Option (List (List Nat))) :=
CompleteNamedSources.lean:124:  let f:=hard2FrontMeter T S c q
CompleteNamedSources.lean:125:  let r:=completeRouteSource W T S c q f.value
CompleteNamedSources.lean:126:  ⟨r.value,f.work+r.work⟩
```

## source-CompleteOrdinaryStep-completeBranchSource_ordinaryCompleteStepSource.txt

```text
CompleteOrdinaryStep.lean:8: def completeBranchSource (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
CompleteOrdinaryStep.lean:9:  Early T S→Charged (Option (List (List Nat)))
CompleteOrdinaryStep.lean:10:  | .common reverse c=>commonBranchMeter FastOrdinary.solve W q T S reverse c
CompleteOrdinaryStep.lean:11:  | .one reverse c=>let p:=Oriented reverse T S;oneSource (cutoff FastOrdinary.solve q) W p.1 p.2 q c.a c.b
CompleteOrdinaryStep.lean:12:  | .high reverse c=>let p:=Oriented reverse T S;highSource (cutoff FastOrdinary.solve q) W p.1 p.2 q c.a c.b
CompleteOrdinaryStep.lean:13:  | .rule4Forward s=>rule4Source (cutoff FastOrdinary.solve q) W s q
CompleteOrdinaryStep.lean:14:  | .rule4Reverse s=>rule4Source (cutoff FastOrdinary.solve q) W s q
CompleteOrdinaryStep.lean:15:  | .hard2 c _=>hard2CompleteSource W T S c q
CompleteOrdinaryStep.lean:16:  | .refused=>⟨none,0⟩

CompleteOrdinaryStep.lean:19: def ordinaryCompleteStepSource (W : GenericForest.FrontierWork.OrdinaryWork) (q : Nat) (T S : Tree) :
CompleteOrdinaryStep.lean:20:  Charged (Option (List (List Nat))) :=
CompleteOrdinaryStep.lean:21:  let f:=meterFront q T S
CompleteOrdinaryStep.lean:22:  match f.value with
CompleteOrdinaryStep.lean:23:  | .stop a=>⟨a,f.work⟩
CompleteOrdinaryStep.lean:24:  | .selected e=>let r:=completeBranchSource W q T S e;⟨r.value,f.work+r.work⟩
```

## source-CutoffFacts-cutoff.txt

```text
CutoffFacts.lean:5: def cutoff (rec : Nat→Tree→Tree→Option CommonForest) (q : Nat) : Tree→Tree→Nat→Option CommonForest :=
CutoffFacts.lean:6:  fun T S r => if r<q then rec r T S else none
```

## source-FastSolve-solve.txt

```text
FastSolve.lean:10: def solve (q : Nat) (T S : Tree) : Option CommonForest :=
FastSolve.lean:11:  if DepthOne.proper T S then
FastSolve.lean:12:   match DepthOne.pretest01 T S with
FastSolve.lean:13:   | .refused => none
FastSolve.lean:14:   | .found c => if DepthOne.cutCost c≤q then some (DepthOne.forest S c) else none
FastSolve.lean:15:   | .rejected =>
FastSolve.lean:16:    let paid := fun u v r => if hr : r<q then solve r u v else none
FastSolve.lean:17:    match early T S with
FastSolve.lean:18:    | .common reverse c =>
FastSolve.lean:19:      let p := commonPair T S reverse c
FastSolve.lean:20:      if hn : (leaves p.1).length<(leaves T).length then
FastSolve.lean:21:        (solve q p.1 p.2).map (expandCommon T S reverse c)
FastSolve.lean:22:      else none
FastSolve.lean:23:    | .one reverse c =>
FastSolve.lean:24:      let p := Oriented reverse T S
FastSolve.lean:25:      runChildren paid p.1 p.2 q [pendantChild p.2 c.a c.b]
FastSolve.lean:26:    | .high reverse c =>
FastSolve.lean:27:      let p := Oriented reverse T S
FastSolve.lean:28:      runChildren paid p.1 p.2 q (branches p.2 c.a c.b)
FastSolve.lean:29:    | .rule4Forward s => runRule4 paid s q
FastSolve.lean:30:    | .rule4Reverse s => runRule4 paid s q
FastSolve.lean:31:    | .hard2 c d => Hard2Dispatcher.run paid T S c d q
FastSolve.lean:32:    | .refused => none
FastSolve.lean:33:  else none
FastSolve.lean:34: termination_by (q,(leaves T).length)
```

## source-ForestProgram-branches_checked_disjointSolve_solve.txt

```text
ForestProgram.lean:9: def checked (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Option Forest :=
ForestProgram.lean:10:   if accepted T ss q F then some F else none

ForestProgram.lean:12: def disjointSolve (t : Tree) (ss : List Tree)
ForestProgram.lean:13:     (ordinary : Tree → Tree → Nat → Option Forest) (q : Nat) : Option Forest :=
ForestProgram.lean:14:   (disjointAttempt t ss ordinary q).bind fun r =>
ForestProgram.lean:15:     r.answers.bind fun xs => checked (some t) ss q (xs.flatMap Prod.snd)

ForestProgram.lean:17: def branches (t : Tree) (ss : List Tree) (h : Overlap) (q : Nat) : List (Nat × Output) :=
ForestProgram.lean:18:   ((raw t ss h.left h.vertex q).map (h.left,·)) ++
ForestProgram.lean:19:     ((raw t ss h.right h.vertex q).map (h.right,·))

ForestProgram.lean:24: def solve (ordinary : Tree → Tree → Nat → Option Forest)
ForestProgram.lean:25:     (T : Option Tree) (ss : List Tree) (q : Nat) : Option Forest :=
ForestProgram.lean:26:   if proper T ss then
ForestProgram.lean:27:     if agrees T ss (ss.map leaves) then some (ss.map leaves) else
ForestProgram.lean:28:     match T, ss with
ForestProgram.lean:29:     | none, _ => none
ForestProgram.lean:30:     | some t, [s] => (ordinary t s q).bind (checked (some t) [s] q)
ForestProgram.lean:31:     | some t, _ =>
ForestProgram.lean:32:       match overlap t ss with
ForestProgram.lean:33:       | none => disjointSolve t ss ordinary q
ForestProgram.lean:34:       | some h =>
ForestProgram.lean:35:         let answers := (branches t ss h q).filterMap fun io =>
ForestProgram.lean:36:           let d := io.2.sourceCuts.length
ForestProgram.lean:37:           if _hd : 1 ≤ d ∧ d ≤ q then solve ordinary T (replace ss io.1 io.2.partition) (q-d)
ForestProgram.lean:38:           else none
ForestProgram.lean:39:         best List.length (accepted T ss q) answers
ForestProgram.lean:40:   else none
ForestProgram.lean:41: termination_by q
```

## source-OWScan-meterPreflight_meterScan.txt

```text
OWScan.lean:16: def meterPreflight (T S : Tree) : Charged (Bool×Nat) :=
OWScan.lean:17:  let p:=meterOrdinaryProper T S;let l:=meterLeaves T;let n:=meterLength l.value
OWScan.lean:18:  ⟨(p.value,n.value),p.work+l.work+n.work+8⟩

OWScan.lean:41: def meterScan (query : Nat→Charged (Option CommonForest)) (start : Nat) : Nat→ScanMeasured
OWScan.lean:42:  | 0=>⟨⟨none,[]⟩,2,2⟩
OWScan.lean:43:  | fuel+1=>let a:=query start
OWScan.lean:44:    match a.value with
OWScan.lean:45:    | some F=>⟨⟨some (start,F),[(start,a.value)]⟩,a.work+12,12⟩
OWScan.lean:46:    | none=>let r:=meterScan query (start+1) fuel
OWScan.lean:47:      ⟨⟨r.value.selected,(start,a.value)::r.value.trials⟩,a.work+r.work+12,r.administration+12⟩
```

## source-OptimizerSourceBodies-sourceFinishMeter_sourceOptimizeMeter.txt

```text
OptimizerSourceBodies.lean:10: def sourceFinishMeter (S : Tree) (r : Scan) : Charged Execution :=
OptimizerSourceBodies.lean:11:  match r.selected with
OptimizerSourceBodies.lean:12:  | none=>⟨⟨r,none,[]⟩,8⟩
OptimizerSourceBodies.lean:13:  | some (_,F)=>
OptimizerSourceBodies.lean:14:   let a:=RecoveryLocalWork.meterRecover S F
OptimizerSourceBodies.lean:15:   ⟨⟨r,a.value,[(F,a.value)]⟩,a.work+12⟩

OptimizerSourceBodies.lean:37: def sourceOptimizeMeter (w : Nat→Nat) (T S : Tree) : Charged Execution :=
OptimizerSourceBodies.lean:38:  let p:=meterPreflight T S
OptimizerSourceBodies.lean:39:  if p.value.1 then
OptimizerSourceBodies.lean:40:   let s:=meterScan (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 p.value.2
OptimizerSourceBodies.lean:41:   let f:=sourceFinishMeter S s.value
OptimizerSourceBodies.lean:42:   ⟨f.value,p.work+s.work+f.work+8⟩
OptimizerSourceBodies.lean:43:  else ⟨⟨⟨none,[]⟩,none,[]⟩,p.work+8⟩
```

## source-OrdinaryChildrenSource-branchesMeter_highSource_oneSource_runChildrenSource.txt

```text
OrdinaryChildrenSource.lean:18: def branchesMeter (S : Tree) (a b : Nat) : Rule5LocalWork.Measured (List Child) :=
OrdinaryChildrenSource.lean:19:  let x:=singletonChildMeter S a;let y:=singletonChildMeter S b;let p:=pendantChildMeter S a b
OrdinaryChildrenSource.lean:20:  ⟨[x.value,y.value,p.value],x.work+y.work+p.work+4⟩

OrdinaryChildrenSource.lean:62: def runChildrenSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree) (q : Nat)
OrdinaryChildrenSource.lean:63:  (cs : List Child) : WholeSourceWork.Charged (Option (List (List Nat))) :=
OrdinaryChildrenSource.lean:64:  let r:=runChildrenMeter actual (fun _=>0) (fun F=>(agreementMeter T S F).work) T S q cs
OrdinaryChildrenSource.lean:65:  ⟨r.value,r.localWork+childForestDebit actual W T q cs⟩

OrdinaryChildrenSource.lean:114: def oneSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree) (q a b : Nat) :
OrdinaryChildrenSource.lean:115:  WholeSourceWork.Charged (Option (List (List Nat))) :=
OrdinaryChildrenSource.lean:116:  let c:=pendantChildMeter S a b
OrdinaryChildrenSource.lean:117:  let r:=runChildrenSource actual W T S q [c.value]
OrdinaryChildrenSource.lean:118:  ⟨r.value,c.work+r.work+2⟩

OrdinaryChildrenSource.lean:120: def highSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree) (q a b : Nat) :
OrdinaryChildrenSource.lean:121:  WholeSourceWork.Charged (Option (List (List Nat))) :=
OrdinaryChildrenSource.lean:122:  let c:=branchesMeter S a b
OrdinaryChildrenSource.lean:123:  let r:=runChildrenSource actual W T S q c.value
OrdinaryChildrenSource.lean:124:  ⟨r.value,c.work+r.work+2⟩
```

## source-Rule4CallerSource-rule4AnswersSource_rule4Source.txt

```text
Rule4CallerSource.lean:66: def rule4AnswersSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
Rule4CallerSource.lean:67:  (q : Nat) : List Rule4.Branch→Charged (List (List (List Nat)))
Rule4CallerSource.lean:68:  | []=>⟨[],1⟩
Rule4CallerSource.lean:69:  | b::bs=>let r:=rule4AnswersSource actual W q bs
Rule4CallerSource.lean:70:   let state:=rule4StateMeter b
Rule4CallerSource.lean:71:   if b.cost≤q then
Rule4CallerSource.lean:72:    let a:=GenericForest.solve actual (some b.target) state.value (q-b.cost)
Rule4CallerSource.lean:73:    ⟨a.toList++r.value,state.work+2*b.cuts.length+8+
Rule4CallerSource.lean:74:      forestWork actual W (some b.target) state.value (q-b.cost)+r.work⟩
Rule4CallerSource.lean:75:   else ⟨r.value,2*b.cuts.length+4+r.work⟩

Rule4CallerSource.lean:89: def rule4Source (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
Rule4CallerSource.lean:90:  {T S : Tree} (s : Rule4.Choice T S) (q : Nat) : Charged (Option (List (List Nat))) :=
Rule4CallerSource.lean:91:  let bs:=rule4BranchesMeter s
Rule4CallerSource.lean:92:  let a:=rule4AnswersSource actual W q bs.value
Rule4CallerSource.lean:93:  let b:=bestLengthMeter (fun _=>⟨true,1⟩) a.value
Rule4CallerSource.lean:94:  ⟨b.value,bs.work+a.work+b.work+2⟩
```

## source-ELOuter-meterFront.txt

```text
ELOuter.lean:19: def meterFront (q : Nat) (T S : Tree) : Charged (Front T S) :=
ELOuter.lean:20:  let p:=meterOrdinaryProper T S
ELOuter.lean:21:  if p.value then
ELOuter.lean:22:   let d:=meterPretest T S
ELOuter.lean:23:   match d.value with
ELOuter.lean:24:   | .refused=>⟨.stop none,p.work+d.work+4⟩
ELOuter.lean:25:   | .found c=>
ELOuter.lean:26:     let f:=meterForest S c
ELOuter.lean:27:     ⟨.stop (if DepthOne.cutCost c≤q then some f.value else none),p.work+d.work+f.work+8⟩
ELOuter.lean:28:   | .rejected=>let e:=meterEarly T S;⟨.selected e.value,p.work+d.work+e.work+4⟩
ELOuter.lean:29:  else ⟨.stop none,p.work+2⟩
```

## source-ELPretest-meterAgreement_meterBest_meterCandidate_meterCandidates_meterComplement_meterForest_meterPretest.txt

```text
ELPretest.lean:5: def meterAgreement (T S : Tree) (F : List (List Nat)) : Charged Bool :=
ELPretest.lean:6:  let t:=meterLeaves T;let pt:=meterPartition t.value F
ELPretest.lean:7:  let s:=meterLeaves S;let ps:=meterPartition s.value F
ELPretest.lean:8:  let shapes:=meterAll (meterRestrictionAgrees T S) F
ELPretest.lean:9:  let et:=meterPairwise T F;let es:=meterPairwise S F
ELPretest.lean:10:  ⟨pt.value&&ps.value&&shapes.value&&et.value&&es.value,
ELPretest.lean:11:   t.work+pt.work+s.work+ps.work+shapes.work+et.work+es.work+8⟩

ELPretest.lean:30: def meterComplement (S : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
ELPretest.lean:31:  let leaves:=meterLeaves S
ELPretest.lean:32:  let f:=meterFilter (fun x=>let a:=meterSubtreeLabels S v;let b:=meterContains x a.value
ELPretest.lean:33:   ⟨!b.value,a.work+b.work+2⟩) leaves.value
ELPretest.lean:34:  ⟨f.value,leaves.work+f.work+2⟩

ELPretest.lean:38: def meterForest (S : Tree) : Option RMAF.Vertex→Charged (List (List Nat))
ELPretest.lean:39:  | none=>let a:=meterLeaves S;⟨[a.value],a.work+2⟩
ELPretest.lean:40:  | some v=>let a:=meterSubtreeLabels S v;let b:=meterComplement S v;⟨[a.value,b.value],a.work+b.work+4⟩

ELPretest.lean:95: def meterBest {α : Type} (cost : α→Nat) (valid : α→Charged Bool) : List α→BestMeasured α
ELPretest.lean:96:  | []=>⟨none,1,[],[],[]⟩
ELPretest.lean:97:  | x::xs=>
ELPretest.lean:98:   let a:=valid x;let r:=meterBest cost valid xs
ELPretest.lean:99:   if a.value then
ELPretest.lean:100:    match r.value with
ELPretest.lean:101:    | none=>⟨some x,a.work+r.work+6,(x,true)::r.checks,xs.length::r.tailSizes,r.comparisons⟩
ELPretest.lean:102:    | some y=>⟨if cost x≤cost y then some x else some y,a.work+r.work+10,
ELPretest.lean:103:      (x,true)::r.checks,xs.length::r.tailSizes,(cost x,cost y)::r.comparisons⟩
ELPretest.lean:104:   else ⟨r.value,a.work+r.work+4,(x,false)::r.checks,xs.length::r.tailSizes,r.comparisons⟩

ELPretest.lean:142: def meterCandidates (S : Tree) : Charged (List (Option RMAF.Vertex)) :=
ELPretest.lean:143:  let e:=meterEdges S
ELPretest.lean:144:  ⟨none::e.value.map some,e.work+4*(e.value.length+1)⟩

ELPretest.lean:151: def meterCandidate (T S : Tree) (c : Option RMAF.Vertex) : Charged Bool :=
ELPretest.lean:152:  let f:=meterForest S c;let a:=meterAgreement T S f.value
ELPretest.lean:153:  ⟨a.value,f.work+a.work+2⟩

ELPretest.lean:157: def meterPretest (T S : Tree) : Charged DepthOne.Result :=
ELPretest.lean:158:  let p:=meterOrdinaryProper T S
ELPretest.lean:159:  if p.value then
ELPretest.lean:160:   let c:=meterCandidates S;let b:=meterBest DepthOne.cutCost (meterCandidate T S) c.value
ELPretest.lean:161:   ⟨match b.value with | none=>.rejected | some c=>.found c,p.work+c.work+b.work+4⟩
ELPretest.lean:162:  else ⟨.refused,p.work+2⟩
```

## source-Pretest-cutCost.txt

```text
Pretest.lean:28: def cutCost : Option Vertex → Nat
Pretest.lean:29:   | none => 0
Pretest.lean:30:   | some _ => 1
```

## source-ActualCaller-actualCallback_rule5AnswerSource.txt

```text
ActualCaller.lean:10: def rule5AnswerSource (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) : Charged (Option Forest) :=
ActualCaller.lean:11:  let r:=source cb W T S a b q
ActualCaller.lean:12:  ⟨match r.value with | .answered answer=>answer | _=>none,r.work+2⟩

ActualCaller.lean:24: def actualCallback (q : Nat) : Ordinary :=cutoff OrdinaryDispatch.FastOrdinary.solve q
```

## source-ActualCaller-actualRule5Source.txt

```text
ActualCaller.lean:26: def actualRule5Source (W : OrdinaryWork) (T S : Tree) (a b q : Nat) :=rule5AnswerSource (actualCallback q) W T S a b q
```

## source-AdmittedCases-SizeTwoSelection.txt

```text
AdmittedCases.lean:5: structure SizeTwoSelection where
AdmittedCases.lean:6:  sourceArc : RMAF.Vertex
AdmittedCases.lean:7:  p : Nat
AdmittedCases.lean:8:  q : Nat
AdmittedCases.lean:9:  deriving Repr, DecidableEq
```

## source-AdmittedCheckCalls-CheckReceipt.txt

```text
AdmittedCheckCalls.lean:16: structure CheckReceipt (α : Type) where
AdmittedCheckCalls.lean:17:  value : α
AdmittedCheckCalls.lean:18:  work : Nat
AdmittedCheckCalls.lean:19:  calls : List CheckRequest
AdmittedCheckCalls.lean:20:  deriving Repr
```

## source-AdmittedCheckCalls-CheckRequest.txt

```text
AdmittedCheckCalls.lean:7: inductive CheckRequest where
AdmittedCheckCalls.lean:8:  | embedding (T : Tree) (P : List (List Nat))
AdmittedCheckCalls.lean:9:  | restriction (T S : Tree) (B : List Nat)
AdmittedCheckCalls.lean:10:  deriving Repr,DecidableEq
```

## source-AdmittedCheckCalls-andSequence.txt

```text
AdmittedCheckCalls.lean:25: def andSequence : List (Unit→CheckReceipt Bool)→CheckReceipt Bool
AdmittedCheckCalls.lean:26:  | []=>⟨true,1,[]⟩
AdmittedCheckCalls.lean:27:  | f::fs=>let a:=f ()
AdmittedCheckCalls.lean:28:            if a.value then let b:=andSequence fs
AdmittedCheckCalls.lean:29:             ⟨b.value,a.work+b.work+a.calls.length+1,a.calls++b.calls⟩
AdmittedCheckCalls.lean:30:            else ⟨false,a.work+1,a.calls⟩
```

## source-AdmittedCheckCalls-checkMeter_liftMeter.txt

```text
AdmittedCheckCalls.lean:22: def liftMeter {α : Type} (m : Measured α) : CheckReceipt α := ⟨m.value,m.work,[]⟩

AdmittedCheckCalls.lean:23: def checkMeter (fee : CheckRequest→Nat) (r : CheckRequest) : CheckReceipt Bool := ⟨checkValue r,fee r,[r]⟩
```

## source-AdmittedCheckCalls-checkValue_restrictionFilterMeter.txt

```text
AdmittedCheckCalls.lean:12: def checkValue : CheckRequest→Bool
AdmittedCheckCalls.lean:13:  | .embedding T P=>pairwiseEmbeddings T P
AdmittedCheckCalls.lean:14:  | .restriction T S B=>restrictionAgrees T S B

AdmittedCheckCalls.lean:61: def restrictionFilterMeter (fee : CheckRequest→Nat) (T S : Tree) : List (List Nat)→CheckReceipt (List (List Nat))
AdmittedCheckCalls.lean:62:  | []=>⟨[],1,[]⟩
AdmittedCheckCalls.lean:63:  | B::P=>let c:=checkMeter fee (.restriction T S B);let r:=restrictionFilterMeter fee T S P
AdmittedCheckCalls.lean:64:            ⟨if c.value then B::r.value else r.value,c.work+r.work+3,.restriction T S B::r.calls⟩
```

## source-AdmittedHandler-Result.txt

```text
AdmittedHandler.lean:6: inductive Result where
AdmittedHandler.lean:7:  | selectorRefused
AdmittedHandler.lean:8:  | paidBuilderRefused
AdmittedHandler.lean:9:  | answered (answer : Option Forest)
AdmittedHandler.lean:10:  deriving DecidableEq, Repr
```

## source-AdmittedRouteBinding-admittedRouteSource.txt

```text
AdmittedRouteBinding.lean:39: def admittedRouteSource (W : OrdinaryWork) (T S : Tree) (c : Candidate) (q : Nat) :=actualRule5Source W T S c.a c.b q
```

## source-AdmittedRule4Guard-admittedRule4Meter.txt

```text
AdmittedRule4Guard.lean:116: def admittedRule4Meter (T S : Tree) : Measured Bool :=
AdmittedRule4Guard.lean:117:  let c:=candidatesMeter T S;let r:=rule4AnyMeter S c.value
AdmittedRule4Guard.lean:118:  ⟨r.value,c.work+r.work+1⟩
```

## source-AdmittedRule4Guard-rule4AnyMeter.txt

```text
AdmittedRule4Guard.lean:92: def rule4AnyMeter (S : Tree) : List Candidate→Measured Bool
AdmittedRule4Guard.lean:93:  | []=>⟨false,1⟩
AdmittedRule4Guard.lean:94:  | c::cs=>let a:=rule4CandidateMeter S c
AdmittedRule4Guard.lean:95:            if a.value then ⟨true,a.work+1⟩ else let r:=rule4AnyMeter S cs;⟨r.value,a.work+r.work+1⟩
```

## source-AdmittedRule4Guard-rule4ArcMeter.txt

```text
AdmittedRule4Guard.lean:7: def rule4ArcMeter (S : Tree) (a b : Nat) (q : RMAF.Vertex) : Measured Bool :=
AdmittedRule4Guard.lean:8:  let l:=subtreeLabelsMeter S q
AdmittedRule4Guard.lean:9:  match l.value with
AdmittedRule4Guard.lean:10:  | [x]=>let c:=hasCherryMeter S a x
AdmittedRule4Guard.lean:11:          if c.value then ⟨true,l.work+c.work+3⟩ else
AdmittedRule4Guard.lean:12:           let d:=hasCherryMeter S b x;⟨d.value,l.work+c.work+d.work+3⟩
AdmittedRule4Guard.lean:13:  | _=>⟨false,l.work+2⟩
```

## source-AdmittedRule4Guard-rule4ArcsMeter.txt

```text
AdmittedRule4Guard.lean:45: def rule4ArcsMeter (S : Tree) (a b : Nat) : List RMAF.Vertex→Measured Bool
AdmittedRule4Guard.lean:46:  | []=>⟨false,1⟩
AdmittedRule4Guard.lean:47:  | q::qs=>let c:=rule4ArcMeter S a b q
AdmittedRule4Guard.lean:48:            if c.value then ⟨true,c.work+1⟩ else let r:=rule4ArcsMeter S a b qs;⟨r.value,c.work+r.work+1⟩
```

## source-AdmittedRule4Guard-rule4CandidateMeter.txt

```text
AdmittedRule4Guard.lean:67: def rule4CandidateMeter (S : Tree) (c : Candidate) : Measured Bool :=
AdmittedRule4Guard.lean:68:  if c.originalCuts.length==2 then
AdmittedRule4Guard.lean:69:   let r:=rule4ArcsMeter S c.a c.b c.originalCuts
AdmittedRule4Guard.lean:70:   ⟨r.value,c.originalCuts.length+r.work+2⟩
AdmittedRule4Guard.lean:71:  else ⟨false,c.originalCuts.length+2⟩
```

## source-AdmittedWork-admittedGuards.txt

```text
AdmittedWork.lean:12: def admittedGuards (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (P : List (List Nat)) : List (Unit→CheckReceipt Bool) :=
AdmittedWork.lean:13:  [fun _=>liftMeter (properPairMeter T S),
AdmittedWork.lean:14:   fun _=>liftMeter (hasCherryMeter T a b),
AdmittedWork.lean:15:   fun _=>liftMeter (earlierMeter T S),fun _=>liftMeter (earlierMeter S T),
AdmittedWork.lean:16:   fun _=>liftMeter (notMeter (admittedRule4Meter T S)),
AdmittedWork.lean:17:   fun _=>liftMeter (notMeter (admittedRule4Meter S T)),
AdmittedWork.lean:18:   fun _=>liftMeter (cutLengthMeter S a b),
AdmittedWork.lean:19:   fun _=>checkMeter fee (.embedding T P),fun _=>checkMeter fee (.embedding S P),
AdmittedWork.lean:20:   fun _=>filteredLengthMeter fee T S P]
```

## source-AdmittedWork-admittedMeter.txt

```text
AdmittedWork.lean:22: def admittedMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt Bool :=
AdmittedWork.lean:23:  let p:=partitionMeter S a b
AdmittedWork.lean:24:  let r:=andSequence (admittedGuards fee T S a b p.value)
AdmittedWork.lean:25:  ⟨r.value,p.work+r.work+1,r.calls⟩
```

## source-AdmittedWork-cutLengthMeter_filteredLengthMeter.txt

```text
AdmittedWork.lean:6: def cutLengthMeter (S : Tree) (a b : Nat) : Measured Bool :=
AdmittedWork.lean:7:  let e:=cutsMeter S a b;⟨e.value.length==2,e.work+e.value.length+2⟩

AdmittedWork.lean:8: def filteredLengthMeter (fee : CheckRequest→Nat) (T S : Tree) (P : List (List Nat)) : CheckReceipt Bool :=
AdmittedWork.lean:9:  let r:=restrictionFilterMeter fee T S P
AdmittedWork.lean:10:  ⟨r.value.length==2,r.work+r.value.length+2,r.calls⟩
```

## source-AllGoodParents-direct.txt

```text
AllGoodParents.lean:6: def direct (P : OrdinaryDispatch.Forest) (q : Nat) : Option OrdinaryDispatch.Forest :=
AllGoodParents.lean:7:  if P.length-1≤q then some P else none
```

## source-BOOptimize-Execution.txt

```text
BOOptimize.lean:5: structure Execution where
BOOptimize.lean:6:  search : Scan
BOOptimize.lean:7:  output : Option CoreProgram.Output
BOOptimize.lean:8:  recoveries : List (CommonForest × Option CoreProgram.Output)
BOOptimize.lean:9:  deriving Repr
```

## source-BOScan-Scan_Trial.txt

```text
BOScan.lean:5: abbrev Trial := Nat × Option CommonForest

BOScan.lean:6: structure Scan where
BOScan.lean:7:  selected : Option (Nat × CommonForest)
BOScan.lean:8:  trials : List Trial
BOScan.lean:9:  deriving Repr
```

## source-BadClassifierWork-badAtMeter.txt

```text
BadClassifierWork.lean:14: def badAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e f : RMAF.Vertex) : CheckReceipt (Option BadSelection) :=
BadClassifierWork.lean:15:  let ne:=eqAddressMeter e f
BadClassifierWork.lean:16:  if ne.value then ⟨none,ne.work+2,[]⟩ else
BadClassifierWork.lean:17:   let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
BadClassifierWork.lean:18:   if c.value then ⟨none,ne.work+l.work+c.work+3,c.calls⟩ else
BadClassifierWork.lean:19:    let s:=subtreeMeter S f
BadClassifierWork.lean:20:    ⟨match s.value with | some (.leaf x)=>some ⟨e,f,x⟩ | _=>none,
BadClassifierWork.lean:21:     ne.work+l.work+c.work+s.work+6,c.calls⟩
```

## source-BadClassifierWork-badCandidatesMeter.txt

```text
BadClassifierWork.lean:145: def badCandidatesMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (List BadSelection) :=
BadClassifierWork.lean:146:  let c:=cutsMeter S a b;let r:=concatMeter (badRowMeter fee T S a b) c.value
BadClassifierWork.lean:147:  ⟨r.value,c.work+r.work+1,r.calls⟩
```

## source-BadClassifierWork-badRowMeter_concatMeter.txt

```text
BadClassifierWork.lean:63: def badRowMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (e : RMAF.Vertex) : CheckReceipt (List BadSelection) :=
BadClassifierWork.lean:64:  let c:=cutsMeter S a b;let r:=optionsMeter (badAtMeter fee T S e) c.value
BadClassifierWork.lean:65:  ⟨r.value,c.work+r.work+1,r.calls⟩

BadClassifierWork.lean:102: def concatMeter {α β : Type} (f : α→CheckReceipt (List β)) : List α→CheckReceipt (List β)
BadClassifierWork.lean:103:  | []=>⟨[],1,[]⟩
BadClassifierWork.lean:104:  | x::xs=>let a:=f x;let r:=concatMeter f xs
BadClassifierWork.lean:105:            ⟨a.value++r.value,a.work+r.work+a.value.length+a.calls.length+2,a.calls++r.calls⟩
```

## source-BadClassifierWork-selectBadMeter.txt

```text
BadClassifierWork.lean:190: def selectBadMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option BadSelection) :=
BadClassifierWork.lean:191:  let c:=badCandidatesMeter fee T S a b;⟨c.value.head?,c.work+1,c.calls⟩
```

## source-BadGroupedPair-Evaluation.txt

```text
BadGroupedPair.lean:8: structure Evaluation where
BadGroupedPair.lean:9:  candidates : List Forest
BadGroupedPair.lean:10:  queries : List (Problem × Nat)
```

## source-BadGroupedPair-PairExecution.txt

```text
BadGroupedPair.lean:35: structure PairExecution where
BadGroupedPair.lean:36:  answer : Option Forest
BadGroupedPair.lean:37:  queries : List (Problem × Nat)
```

## source-BadPairSource-badPairLocalSource.txt

```text
BadPairSource.lean:9: def badPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
BadPairSource.lean:10:  (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
BadPairSource.lean:11:  let good:=meterRestrictionAgrees S T C
BadPairSource.lean:12:  if good.value then
BadPairSource.lean:13:   let r:=bothBadLocalPairLocalSource actual S T A B C edge q
BadPairSource.lean:14:   ⟨r.value,good.work+r.work+8⟩
BadPairSource.lean:15:  else
BadPairSource.lean:16:   let r:=groupPairLocalSource actual T S A B C edge q
BadPairSource.lean:17:   ⟨⟨r.value.answer,groupCalls r.value.queries⟩,good.work+r.work+12*r.value.queries.length+12⟩
```

## source-BadPairSource-badPairSource.txt

```text
BadPairSource.lean:25: def badPairSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (T S : Tree)
BadPairSource.lean:26:  (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
BadPairSource.lean:27:  let r:=badPairLocalSource actual T S A B C edge q
BadPairSource.lean:28:  ⟨r.value,r.work+callsForestDebit actual W r.value.calls⟩
```

## source-BlockCost-meterBlocks.txt

```text
BlockCost.lean:81: def meterBlocks (p : Paint) : Charged (List (List Nat)) :=
BlockCost.lean:82:  let m := meterSplit p
BlockCost.lean:83:  let n := meterNonempty (m.value.1::m.value.2)
BlockCost.lean:84:  ⟨n.value,m.work+n.work+8⟩
```

## source-BlockCost-meterNonempty_meterSplit.txt

```text
BlockCost.lean:34: def meterSplit : Paint→Charged (List Nat×List (List Nat))
BlockCost.lean:35:  | .leaf x _ => ⟨([x],[]),8⟩
BlockCost.lean:36:  | .node c l r =>
BlockCost.lean:37:   let a := meterSplit l
BlockCost.lean:38:   let b := meterSplit r
BlockCost.lean:39:   let la := if c==root l then a.value.1 else []
BlockCost.lean:40:   let lb := if c==root r then b.value.1 else []
BlockCost.lean:41:   let fa := if c==root l then a.value.2 else a.value.1::a.value.2
BlockCost.lean:42:   let fb := if c==root r then b.value.2 else b.value.1::b.value.2
BlockCost.lean:43:   ⟨(la++lb,fa++fb),a.work+b.work+4*(la.length+fa.length+2)+16⟩

BlockCost.lean:66: def meterNonempty : List (List Nat)→Charged (List (List Nat))
BlockCost.lean:67:  | [] => ⟨[],4⟩
BlockCost.lean:68:  | B::F =>
BlockCost.lean:69:   let m := meterNonempty F
BlockCost.lean:70:   ⟨if B.isEmpty then m.value else B::m.value,m.work+8⟩
```

## source-BothBadLocalExecutionSource-bothBadDispatchLocalSource.txt

```text
BothBadLocalExecutionSource.lean:20: def bothBadDispatchLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree) (e : Entry) : SourceExecution:=
BothBadLocalExecutionSource.lean:21:  match e.mode with
BothBadLocalExecutionSource.lean:22:  | .ordinary=>ordinaryLocalSource actual T S e.output.partition e.budget
BothBadLocalExecutionSource.lean:23:  | .full=>let ss:=sourceForestMeter S e.output.partition
BothBadLocalExecutionSource.lean:24:           ⟨⟨GenericForest.solve actual (some T) ss.value e.budget,[⟨some T,ss.value,e.budget⟩]⟩,ss.work+16⟩
BothBadLocalExecutionSource.lean:25:  | .retained _ residual completed known=>
BothBadLocalExecutionSource.lean:26:    let t:=localTargetMeter (some T) residual
BothBadLocalExecutionSource.lean:27:    let sf:=sourceForestMeter S e.output.partition
BothBadLocalExecutionSource.lean:28:    let bs:=ownedMeter sf.value residual
BothBadLocalExecutionSource.lean:29:    let a:=GenericForest.solve actual t.value bs.value e.budget
BothBadLocalExecutionSource.lean:30:    let f:=retainedReconstructionMeter known completed a
BothBadLocalExecutionSource.lean:31:    ⟨⟨f.value,[⟨t.value,bs.value,e.budget⟩]⟩,t.work+sf.work+bs.work+f.work+20⟩
```

## source-BothBadLocalExecutionSource-bothBadExecuteLocalSource.txt

```text
BothBadLocalExecutionSource.lean:38: def bothBadExecuteLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
BothBadLocalExecutionSource.lean:39:  (q : Nat) : List Entry→SourceExecution
BothBadLocalExecutionSource.lean:40:  | []=>⟨⟨none,[]⟩,2⟩
BothBadLocalExecutionSource.lean:41:  | e::es=>let r:=bothBadDispatchLocalSource actual T S e
BothBadLocalExecutionSource.lean:42:    let tail:=bothBadExecuteLocalSource actual T S q es
BothBadLocalExecutionSource.lean:43:    let checked:=checkedMeter T S q r.value.answer
BothBadLocalExecutionSource.lean:44:    let best:=chooseMeter checked.value tail.value.answer
BothBadLocalExecutionSource.lean:45:    ⟨⟨best.value,r.value.calls++tail.value.calls⟩,
BothBadLocalExecutionSource.lean:46:     r.work+tail.work+checked.work+best.work+2*r.value.calls.length+20⟩
```

## source-BothBadLocalExecutionSource-bothBadLocalPairLocalSource.txt

```text
BothBadLocalExecutionSource.lean:55: def bothBadLocalPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
BothBadLocalExecutionSource.lean:56:  (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : SourceExecution:=
BothBadLocalExecutionSource.lean:57:  let d:=pairDescendantsMeter T edge.2
BothBadLocalExecutionSource.lean:58:  let p:=bothBadPlanMeter S T A B C d.value q
BothBadLocalExecutionSource.lean:59:  let e:=bothBadExecuteLocalSource actual T S q p.value
BothBadLocalExecutionSource.lean:60:  ⟨e.value,d.work+p.work+e.work+12⟩
```

## source-BothBadLocalExecutionSource-retainedReconstructionMeter.txt

```text
BothBadLocalExecutionSource.lean:10: def retainedReconstructionMeter (known : List (List Nat)) (completed : List Nat)
BothBadLocalExecutionSource.lean:11:  (answer : Option (List (List Nat))) : Charged (Option (List (List Nat))):=
BothBadLocalExecutionSource.lean:12:  match answer with
BothBadLocalExecutionSource.lean:13:  | none=>⟨none,4⟩
BothBadLocalExecutionSource.lean:14:  | some F=>⟨some (known++F++[completed]),4*known.length+2*F.length+16⟩
```

## source-BothBadPlanSource-bothBadPlanMeter.txt

```text
BothBadPlanSource.lean:43: def bothBadPlanMeter (S T : Tree) (A B C D : List Nat) (q : Nat) : Charged (List Entry):=
BothBadPlanSource.lean:44:  if q<3 then ⟨[],4⟩ else
BothBadPlanSource.lean:45:   let a:=generatedOutputsMeter S (cheapColorMeter A B D) 3
BothBadPlanSource.lean:46:   let b:=generatedOutputsMeter S (cheapColorMeter B A D) 3
BothBadPlanSource.lean:47:   if a.value.isEmpty then
BothBadPlanSource.lean:48:    if b.value.isEmpty then
BothBadPlanSource.lean:49:     let x:=generatedOutputsMeter S (cheapColorMeter A B D) q
BothBadPlanSource.lean:50:     let y:=generatedOutputsMeter S (cheapColorMeter B A D) q
BothBadPlanSource.lean:51:     let outputs:=appendOutputsMeter x y
BothBadPlanSource.lean:52:     let entries:=entriesMeter q .full outputs.value
BothBadPlanSource.lean:53:     ⟨entries.value,a.work+b.work+outputs.work+entries.work+16⟩
BothBadPlanSource.lean:54:    else
BothBadPlanSource.lean:55:     let opposite:=reuseOutputsMeter S (cheapColorMeter A B D) a.value q
BothBadPlanSource.lean:56:     let cp:=cheapPlanMeter S T B A C D q b.value opposite.value
BothBadPlanSource.lean:57:     ⟨cp.value,a.work+b.work+opposite.work+cp.work+16⟩
BothBadPlanSource.lean:58:   else
BothBadPlanSource.lean:59:    let opposite:=reuseOutputsMeter S (cheapColorMeter B A D) b.value q
BothBadPlanSource.lean:60:    let cp:=cheapPlanMeter S T A B C D q a.value opposite.value
BothBadPlanSource.lean:61:    ⟨cp.value,a.work+b.work+opposite.work+cp.work+16⟩
```

## source-BothBadPlanSource-cheapPlanMeter_reuseOutputsMeter.txt

```text
BothBadPlanSource.lean:7: def cheapPlanMeter (S T : Tree) (A B C D : List Nat) (q : Nat)
BothBadPlanSource.lean:8:  (cheap opposite : List CoreProgram.Output) : Charged (List Entry):=
BothBadPlanSource.lean:9:  let y:=yesSideMeter A D;let n:=noSideMeter A D
BothBadPlanSource.lean:10:  let gy:=meterRestrictionAgrees S T y.value;let gn:=meterRestrictionAgrees S T n.value
BothBadPlanSource.lean:11:  let front:=y.work+n.work+gy.work+gn.work+12
BothBadPlanSource.lean:12:  if gy.value&&gn.value then
BothBadPlanSource.lean:13:   let known:=knownOneMeter T S A
BothBadPlanSource.lean:14:   match known.value with
BothBadPlanSource.lean:15:   | none=>⟨[],front+known.work+8⟩
BothBadPlanSource.lean:16:   | some F=>let a:=entriesMeter q .ordinary cheap
BothBadPlanSource.lean:17:             let b:=entriesMeter q (.retained A B C F) opposite
BothBadPlanSource.lean:18:             let both:=appendEntriesMeter a b
BothBadPlanSource.lean:19:             ⟨both.value,front+known.work+both.work+12⟩
BothBadPlanSource.lean:20:  else
BothBadPlanSource.lean:21:   let a:=entriesMeter q .ordinary cheap;let b:=entriesMeter q .full opposite
BothBadPlanSource.lean:22:   let both:=appendEntriesMeter a b
BothBadPlanSource.lean:23:   ⟨both.value,front+both.work+8⟩

BothBadPlanSource.lean:33: def reuseOutputsMeter (S : Tree) (color : Nat→Charged Nat) (probe : List CoreProgram.Output) (q : Nat) : Charged (List CoreProgram.Output):=
BothBadPlanSource.lean:34:  if probe.isEmpty then let r:=generatedOutputsMeter S color q;⟨r.value,r.work+4⟩ else ⟨probe,4⟩
```

## source-BothBadPlannerAtoms-appendEntriesMeter_knownOneMeter_noSideMeter_yesSideMeter.txt

```text
BothBadPlannerAtoms.lean:12: def yesSideMeter (A D : List Nat) : Charged (List Nat):=meterFilter (fun x=>meterContains x D) A

BothBadPlannerAtoms.lean:13: def noSideMeter (A D : List Nat) : Charged (List Nat):=
BothBadPlannerAtoms.lean:14:  meterFilter (fun x=>let r:=meterContains x D;⟨!r.value,r.work+2⟩) A

BothBadPlannerAtoms.lean:20: def knownOneMeter (T S : Tree) (A : List Nat) : Charged (Option (List (List Nat))):=
BothBadPlannerAtoms.lean:21:  let t:=meterRestrict A T;let s:=meterRestrict A S
BothBadPlannerAtoms.lean:22:  match t.value,s.value with
BothBadPlannerAtoms.lean:23:  | some t',some s'=>let p:=meterPretest t' s'
BothBadPlannerAtoms.lean:24:    match p.value with
BothBadPlannerAtoms.lean:25:    | .found (some v)=>let f:=meterForest s' (some v);⟨some f.value,t.work+s.work+p.work+f.work+16⟩
BothBadPlannerAtoms.lean:26:    | _=>⟨none,t.work+s.work+p.work+12⟩
BothBadPlannerAtoms.lean:27:  | _,_=>⟨none,t.work+s.work+8⟩

BothBadPlannerAtoms.lean:52: def appendEntriesMeter (a b : Charged (List Entry)) : Charged (List Entry):=
BothBadPlannerAtoms.lean:53:  ⟨a.value++b.value,a.work+b.work+2*a.value.length+4⟩
```

## source-BothBadPlannerAtoms-cheapColorMeter_entriesMeter.txt

```text
BothBadPlannerAtoms.lean:7: def cheapColorMeter (A B D : List Nat) (x : Nat) : Charged Nat:=sideTaggedMeter B A D x

BothBadPlannerAtoms.lean:38: def entriesMeter (q : Nat) (mode : Mode) : List CoreProgram.Output→Charged (List Entry)
BothBadPlannerAtoms.lean:39:  | []=>⟨[],2⟩
BothBadPlannerAtoms.lean:40:  | o::os=>let r:=entriesMeter q mode os
BothBadPlannerAtoms.lean:41:    ⟨if o.sourceCuts.length+mode.extra≤q then
BothBadPlannerAtoms.lean:42:       ⟨o,mode,q-o.sourceCuts.length-mode.extra⟩::r.value else r.value,
BothBadPlannerAtoms.lean:43:      2*o.sourceCuts.length+r.work+20⟩
```

## source-BoundaryClassifierWork-boundaryMeter.txt

```text
BoundaryClassifierWork.lean:7: def boundaryMeter (T : Tree) (X : List Nat) (c : Nat) : Measured (Option BoundarySelection) :=
BoundaryClassifierWork.lean:8:  let i:=incidentMeter T X
BoundaryClassifierWork.lean:9:  match i.value with
BoundaryClassifierWork.lean:10:  | [q]=>⟨some (.one q),i.work+3⟩
BoundaryClassifierWork.lean:11:  | [q,r]=>
BoundaryClassifierWork.lean:12:   let ou:=outsideCheckMeter T X q c
BoundaryClassifierWork.lean:13:   let u:=if ou.value then q else r
BoundaryClassifierWork.lean:14:   let ov:=outsideCheckMeter T X q c
BoundaryClassifierWork.lean:15:   let v:=if ov.value then r else q
BoundaryClassifierWork.lean:16:   let p:=paintMeter T X u
BoundaryClassifierWork.lean:17:   if p.value then ⟨some (.third u v),i.work+ou.work+ov.work+p.work+7⟩ else
BoundaryClassifierWork.lean:18:    let s:=paintMeter T X v
BoundaryClassifierWork.lean:19:    ⟨if s.value then some (.first u v) else some (.second u v),i.work+ou.work+ov.work+p.work+s.work+8⟩
BoundaryClassifierWork.lean:20:  | _=>⟨none,i.work+2⟩
```

## source-Bridge-colorLabel.txt

```text
Bridge.lean:552: def colorLabel (t : RMAF.Tree) (v : Vertex) (x : Nat) : Nat :=
Bridge.lean:553:   region v ((leafList [x] t).headD [])
```

## source-Bridge-leafList.txt

```text
Bridge.lean:399: def leafList (D : List Nat) : RMAF.Tree → List Vertex
Bridge.lean:400:   | .leaf x => if D.contains x then [[]] else []
Bridge.lean:401:   | .node l r => RMAF.prependSide false (leafList D l) ++
Bridge.lean:402:       RMAF.prependSide true (leafList D r)
```

## source-BuildSetup-labelMax.txt

```text
BuildSetup.lean:5: def labelMax (L : List Nat) : Nat := L.foldr Nat.max 0
```

## source-CallerSetup-Setup.txt

```text
CallerSetup.lean:8: structure Setup where
CallerSetup.lean:9:   T : Tree
CallerSetup.lean:10:   S : Tree
CallerSetup.lean:11:   tx : Tree
CallerSetup.lean:12:   sx : Tree
CallerSetup.lean:13:   ty : Tree
CallerSetup.lean:14:   sy : Tree
CallerSetup.lean:15:   mxT : Tree
CallerSetup.lean:16:   mxS : Tree
CallerSetup.lean:17:   myT : Tree
CallerSetup.lean:18:   myS : Tree
CallerSetup.lean:19:   X : List Nat
CallerSetup.lean:20:   Y : List Nat
CallerSetup.lean:21:   x : Nat
CallerSetup.lean:22:   y : Nat
CallerSetup.lean:23:   rho : Nat
CallerSetup.lean:24:   gamma : Nat
CallerSetup.lean:25:   nt : (leaves T).Nodup
CallerSetup.lean:26:   ns : (leaves S).Nodup
CallerSetup.lean:27:   hpT : partitionCheck (leaves T) [X,Y]=true
CallerSetup.lean:28:   hpS : partitionCheck (leaves S) [X,Y]=true
CallerSetup.lean:29:   edgeT : OriginalSplit T X Y
CallerSetup.lean:30:   edgeS : OriginalSplit S X Y
CallerSetup.lean:31:   htx : restrict X T=some tx
CallerSetup.lean:32:   hsx : restrict X S=some sx
CallerSetup.lean:33:   hty : restrict Y T=some ty
CallerSetup.lean:34:   hsy : restrict Y S=some sy
CallerSetup.lean:35:   hMXT : marked T X y rho=some mxT
CallerSetup.lean:36:   hMXS : marked S X y rho=some mxS
CallerSetup.lean:37:   hMYT : marked T Y x gamma=some myT
CallerSetup.lean:38:   hMYS : marked S Y x gamma=some myS
CallerSetup.lean:39:   hx : x∈X
CallerSetup.lean:40:   hy : y∈Y
CallerSetup.lean:41:   frT : rho∉leaves T
CallerSetup.lean:42:   frS : rho∉leaves S
CallerSetup.lean:43:   fgT : gamma∉leaves T
CallerSetup.lean:44:   fgS : gamma∉leaves S
```

## source-CandidateCost-meterCandidate.txt

```text
CandidateCost.lean:5: def meterCandidate (T : Option Tree) (ss : List Tree) : Charged (List (List Nat)) :=
CandidateCost.lean:6:  match T with
CandidateCost.lean:7:  | none => ⟨[],4⟩
CandidateCost.lean:8:  | some t =>
CandidateCost.lean:9:   let p := meterSolve (List.range ss.length) (fun x=>meterOwner x ss) t
CandidateCost.lean:10:   let b := meterBlocks p.value
CandidateCost.lean:11:   ⟨b.value,p.work+b.work+4*(ss.length+1)+8⟩
```

## source-Case322Caller-Branch.txt

```text
Case322Caller.lean:27: structure Branch where
Case322Caller.lean:28:  role : Role
Case322Caller.lean:29:  originalCuts : List RMAF.Vertex
Case322Caller.lean:30:  partition : List (List Nat)
Case322Caller.lean:31:  deriving DecidableEq,Repr
```

## source-Case322Caller-Role_current.txt

```text
Case322Caller.lean:26: inductive Role where | target | source deriving DecidableEq,Repr

Case322Caller.lean:33: def current (T S : Tree) (c : Branch) : Tree := if c.role = .source then S else T
```

## source-CheckAssembly-meterAgrees.txt

```text
CheckAssembly.lean:39: def meterAgrees (T : Option Tree) (ss : List Tree) (F : Forest) : Charged Bool :=
CheckAssembly.lean:40:  let p:=meterProper T ss;let a:=meterLabels T;let f:=meterPartition a.value F
CheckAssembly.lean:41:  let c:=meterAll (fun B=>meterSourceContainment B ss) F
CheckAssembly.lean:42:  let e:=meterTargetEmbeddings T F;let s:=meterAll (meterSourceCheck T F) ss
CheckAssembly.lean:43:  ⟨p.value&&f.value&&c.value&&e.value&&s.value,p.work+a.work+f.work+c.work+e.work+s.work+8⟩
```

## source-CheckAssembly-meterLabels.txt

```text
CheckAssembly.lean:5: def meterLabels : Option Tree → Charged (List Nat)
CheckAssembly.lean:6:  | none=>⟨[],1⟩ | some t=>meterLeaves t
```

## source-CheckAssembly-meterProper_meterTargetAgrees.txt

```text
CheckAssembly.lean:9: def meterProper (T : Option Tree) (ss : List Tree) : Charged Bool :=
CheckAssembly.lean:10:  let a:=meterLabels T;let b:=meterNodup a.value;let c:=meterSourceLeaves ss
CheckAssembly.lean:11:  let d:=meterPartition a.value c.value
CheckAssembly.lean:12:  ⟨b.value&&d.value,a.work+b.work+c.work+d.work+4⟩

CheckAssembly.lean:15: def meterTargetAgrees : Option Tree → Tree → List Nat → Charged Bool
CheckAssembly.lean:16:  | none,_,_=>⟨false,1⟩ | some t,s,B=>meterRestrictionAgrees t s B
```

## source-CheckAssembly-meterSourceCheck_meterSourceContainment_meterTargetEmbeddings.txt

```text
CheckAssembly.lean:20: def meterTargetEmbeddings : Option Tree → Forest → Charged Bool
CheckAssembly.lean:21:  | none,F=>⟨F.isEmpty,1⟩ | some t,F=>meterPairwise t F

CheckAssembly.lean:25: def meterSourceCheck (T : Option Tree) (F : Forest) (s : Tree) : Charged Bool :=
CheckAssembly.lean:26:  let a:=meterLeaves s;let G:=meterFamily a.value F
CheckAssembly.lean:27:  let b:=meterLeaves s;let p:=meterPartition b.value G.value
CheckAssembly.lean:28:  let r:=meterAll (meterTargetAgrees T s) G.value
CheckAssembly.lean:29:  let e:=meterPairwise s G.value
CheckAssembly.lean:30:  ⟨p.value&&r.value&&e.value,a.work+G.work+b.work+p.work+r.work+e.work+8⟩

CheckAssembly.lean:34: def meterSourceContainment (B : List Nat) (ss : List Tree) : Charged Bool :=
CheckAssembly.lean:35:  meterAny (fun s=>let a:=meterLeaves s;let c:=meterContained B a.value;⟨c.value,a.work+c.work+2⟩) ss
```

## source-CheckFamilies-meterContained.txt

```text
CheckFamilies.lean:40: def meterContained (B U : List Nat) := meterAll (fun x=>meterContains x U) B
```

## source-CheckFamilies-meterFamily.txt

```text
CheckFamilies.lean:49: def meterFamily (U : List Nat) : Forest → Charged Forest
CheckFamilies.lean:50:  | []=>⟨[],1⟩
CheckFamilies.lean:51:  | B::F=>let c:=meterContained B U;let r:=meterFamily U F
CheckFamilies.lean:52:          ⟨if c.value then B::r.value else r.value,c.work+r.work+6⟩
```

## source-CheckFamilies-meterLeaves_meterNodup.txt

```text
CheckFamilies.lean:8: def meterLeaves : Tree → Charged (List Nat)
CheckFamilies.lean:9:  | .leaf x=>⟨[x],4⟩
CheckFamilies.lean:10:  | .node l r=>let a:=meterLeaves l;let b:=meterLeaves r
CheckFamilies.lean:11:               ⟨a.value++b.value,a.work+b.work+6*(a.value.length+1)⟩

CheckFamilies.lean:25: def meterNodup : List Nat → Charged Bool
CheckFamilies.lean:26:  | []=>⟨true,1⟩
CheckFamilies.lean:27:  | x::xs=>let c:=meterContains x xs;let r:=meterNodup xs;⟨!c.value&&r.value,c.work+r.work+4⟩
```

## source-CheckFamilies-meterSourceLeaves.txt

```text
CheckFamilies.lean:75: def meterSourceLeaves : List Tree → Charged Forest
CheckFamilies.lean:76:  | []=>⟨[],1⟩
CheckFamilies.lean:77:  | s::ss=>let a:=meterLeaves s;let r:=meterSourceLeaves ss
CheckFamilies.lean:78:           ⟨a.value::r.value,a.work+r.work+4⟩
```

## source-CheckPrimitives-meterAll_meterCount_meterFlatten.txt

```text
CheckPrimitives.lean:6: def meterAll {α : Type} (f : α → Charged Bool) : List α → Charged Bool
CheckPrimitives.lean:7:  | [] => ⟨true,1⟩
CheckPrimitives.lean:8:  | x::xs => let a:=f x;let r:=meterAll f xs;⟨a.value && r.value,a.work+r.work+4⟩

CheckPrimitives.lean:42: def meterCount (x : Nat) : List Nat → Charged Nat
CheckPrimitives.lean:43:  | [] => ⟨0,1⟩
CheckPrimitives.lean:44:  | y::ys => let r:=meterCount x ys;⟨(if x==y then 1 else 0)+r.value,r.work+4⟩

CheckPrimitives.lean:58: def meterFlatten {α : Type} : List (List α) → Charged (List α)
CheckPrimitives.lean:59:  | [] => ⟨[],1⟩
CheckPrimitives.lean:60:  | x::xs => let r:=meterFlatten xs;⟨x++r.value,6*(x.length+1)+r.work⟩
```

## source-CheckPrimitives-meterAny.txt

```text
CheckPrimitives.lean:10: def meterAny {α : Type} (f : α → Charged Bool) : List α → Charged Bool
CheckPrimitives.lean:11:  | [] => ⟨false,1⟩
CheckPrimitives.lean:12:  | x::xs => let a:=f x;let r:=meterAny f xs;⟨a.value || r.value,a.work+r.work+4⟩
```

## source-CheckPrimitives-meterPartition.txt

```text
CheckPrimitives.lean:70: def meterPartition (L : List Nat) (F : List (List Nat)) : Charged Bool :=
CheckPrimitives.lean:71:  let nonempty:=meterAll (fun B : List Nat=>⟨!B.isEmpty,1⟩) F
CheckPrimitives.lean:72:  let counts:=meterAll (fun x=>let cells:=meterFlatten F;let count:=meterCount x cells.value;
CheckPrimitives.lean:73:   ⟨count.value==1,cells.work+count.work+4⟩) L
CheckPrimitives.lean:74:  let cells:=meterFlatten F
CheckPrimitives.lean:75:  let labels:=meterAll (fun x=>meterContains x L) cells.value
CheckPrimitives.lean:76:  ⟨nonempty.value && counts.value && labels.value,nonempty.work+counts.work+cells.work+labels.work+4⟩
```

## source-CheckedMerge-bestMeter.txt

```text
CheckedMerge.lean:5: def bestMeter (check : Forest→Measured Bool) : List Forest→Measured (Option Forest)
CheckedMerge.lean:6:  | [] => ⟨none,1⟩
CheckedMerge.lean:7:  | G::gs => let c:=check G;let r:=bestMeter check gs
CheckedMerge.lean:8:             let v:=if c.value then
CheckedMerge.lean:9:                match r.value with
CheckedMerge.lean:10:                | none => some G
CheckedMerge.lean:11:                | some H => if G.length-1≤H.length-1 then some G else some H
CheckedMerge.lean:12:               else r.value
CheckedMerge.lean:13:                                                                             
CheckedMerge.lean:14:                                                     
CheckedMerge.lean:15:             ⟨v,c.work+r.work+G.length+(r.value.map List.length).getD 0+4⟩
```

## source-CheckedMerge-pickMeter.txt

```text
CheckedMerge.lean:100: def pickMeter (check : Forest→Measured Bool) (X Y : List Nat) (x y rho gamma : Nat)
CheckedMerge.lean:101:  (FM FN : Forest) : Measured (Option Forest) :=
CheckedMerge.lean:102:  let r:=mergeMeter X Y x y rho gamma FM FN
CheckedMerge.lean:103:  let b:=bestMeter check r.value
CheckedMerge.lean:104:  ⟨b.value,r.work+b.work⟩
```

## source-CherryGuardWork-CherryRow_cherryAnyMeter.txt

```text
CherryGuardWork.lean:4: abbrev CherryRow := RMAF.Vertex×Nat×Nat

CherryGuardWork.lean:55: def cherryAnyMeter (a b : Nat) : List CherryRow→Measured Bool
CherryGuardWork.lean:56:  | []=>⟨false,1⟩
CherryGuardWork.lean:57:  | c::cs=>if endpointGuard a b c then ⟨true,8⟩ else
CherryGuardWork.lean:58:            let r:=cherryAnyMeter a b cs;⟨r.value,r.work+8⟩
```

## source-CherryGuardWork-cherriesMeter_hasCherryMeter.txt

```text
CherryGuardWork.lean:6: def cherriesMeter : Tree→Measured (List CherryRow)
CherryGuardWork.lean:7:  | .leaf _=>⟨[],1⟩
CherryGuardWork.lean:8:  | .node (.leaf a) (.leaf b)=>⟨[([],a,b)],3⟩
CherryGuardWork.lean:9:  | .node l r=>let a:=cherriesMeter l;let b:=cherriesMeter r
CherryGuardWork.lean:10:                ⟨a.value.map (fun (p,x,y)=>(false::p,x,y))++
CherryGuardWork.lean:11:                 b.value.map (fun (p,x,y)=>(true::p,x,y)),
CherryGuardWork.lean:12:                 a.work+b.work+6*a.value.length+5*b.value.length+3⟩

CherryGuardWork.lean:72: def hasCherryMeter (T : Tree) (a b : Nat) : Measured Bool :=
CherryGuardWork.lean:73:  let c:=cherriesMeter T;let r:=cherryAnyMeter a b c.value
CherryGuardWork.lean:74:  ⟨r.value,c.work+r.work+1⟩
```

## source-CherryGuardWork-endpointGuard.txt

```text
CherryGuardWork.lean:52: def endpointGuard (a b : Nat) (c : CherryRow) : Bool :=
CherryGuardWork.lean:53:  let (_,x,y):=c;(x==a && y==b)||(x==b && y==a)
```

## source-ChildrenExecutionWork-ChildrenReceipt.txt

```text
ChildrenExecutionWork.lean:162: structure ChildrenReceipt where
ChildrenExecutionWork.lean:163:  value : Option Forest
ChildrenExecutionWork.lean:164:  localWork : Nat
ChildrenExecutionWork.lean:165:  recursiveWork : Nat
ChildrenExecutionWork.lean:166:  calls : List ForestQuery
ChildrenExecutionWork.lean:167:  agreementChecks : List Forest
ChildrenExecutionWork.lean:168:  deriving Repr
```

## source-ChildrenExecutionWork-ForestQuery_ForestReceipt_childExecutionMeter.txt

```text
ChildrenExecutionWork.lean:8: structure ForestQuery where
ChildrenExecutionWork.lean:9:  child : Child
ChildrenExecutionWork.lean:10:  budget : Nat
ChildrenExecutionWork.lean:11:  deriving Repr,DecidableEq

ChildrenExecutionWork.lean:12: structure ForestReceipt (α : Type) where
ChildrenExecutionWork.lean:13:  value : α
ChildrenExecutionWork.lean:14:  localWork : Nat
ChildrenExecutionWork.lean:15:  recursiveWork : Nat
ChildrenExecutionWork.lean:16:  calls : List ForestQuery
ChildrenExecutionWork.lean:17:  deriving Repr

ChildrenExecutionWork.lean:21: def childExecutionMeter (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) (c : Child) : ForestReceipt (Option Forest) :=
ChildrenExecutionWork.lean:22:  if c.paid≤q then
ChildrenExecutionWork.lean:23:   let r:=q-c.paid;let call:ForestQuery:=⟨c,r⟩
ChildrenExecutionWork.lean:24:   ⟨GenericForest.solve actual (some T) c.sourceForest r,4,fee call,[call]⟩
ChildrenExecutionWork.lean:25:  else ⟨none,2,0,[]⟩
```

## source-ChildrenExecutionWork-acceptedMeter_bestLengthMeter_childrenAnswersMeter.txt

```text
ChildrenExecutionWork.lean:32: def childrenAnswersMeter (actual : Ordinary) (fee : ForestQuery→Nat) (T : Tree) (q : Nat) : List Child→ForestReceipt (List Forest)
ChildrenExecutionWork.lean:33:  | []=>⟨[],1,0,[]⟩
ChildrenExecutionWork.lean:34:  | c::cs=>let a:=childExecutionMeter actual fee T q c;let r:=childrenAnswersMeter actual fee T q cs
ChildrenExecutionWork.lean:35:   ⟨match a.value with | none=>r.value | some F=>F::r.value,
ChildrenExecutionWork.lean:36:    a.localWork+r.localWork+a.calls.length+3,a.recursiveWork+r.recursiveWork,a.calls++r.calls⟩

ChildrenExecutionWork.lean:117: def acceptedMeter (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (F : Forest) : Measured Bool :=
ChildrenExecutionWork.lean:118:  ⟨agreement T S F && decide (F.length-1≤q),agreementFee F+F.length+3⟩

ChildrenExecutionWork.lean:122: def bestLengthMeter (check : Forest→Measured Bool) : List Forest→Measured (Option Forest)
ChildrenExecutionWork.lean:123:  | []=>⟨none,1⟩
ChildrenExecutionWork.lean:124:  | F::fs=>let c:=check F;let r:=bestLengthMeter check fs
ChildrenExecutionWork.lean:125:   ⟨if c.value then match r.value with | none=>some F | some G=>if F.length≤G.length then some F else some G else r.value,
ChildrenExecutionWork.lean:126:    c.work+r.work+F.length+(r.value.map List.length).getD 0+4⟩
```

## source-ClassifierAtoms-optionsMeter.txt

```text
ClassifierAtoms.lean:27: def optionsMeter {α β : Type} (f : α→CheckReceipt (Option β)) : List α→CheckReceipt (List β)
ClassifierAtoms.lean:28:  | []=>⟨[],1,[]⟩
ClassifierAtoms.lean:29:  | x::xs=>let a:=f x;let r:=optionsMeter f xs
ClassifierAtoms.lean:30:            ⟨match a.value with | some y=>y::r.value | none=>r.value,
ClassifierAtoms.lean:31:             a.work+r.work+a.calls.length+3,a.calls++r.calls⟩
```

## source-ClassifierAtoms-outsideCheckMeter_paintMeter.txt

```text
ClassifierAtoms.lean:77: def paintMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Measured Bool :=
ClassifierAtoms.lean:78:  let m:=minimalMeter X T;let c:=containsAddressMeter q m.value
ClassifierAtoms.lean:79:  ⟨c.value,m.work+c.work+1⟩

ClassifierAtoms.lean:99: def outsideCheckMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) (x : Nat) : Measured Bool :=
ClassifierAtoms.lean:100:  let l:=subtreeLabelsMeter T q;let c:=containsMeter x l.value;let p:=paintMeter T X q
ClassifierAtoms.lean:101:  ⟨c.value != p.value,l.work+c.work+p.work+2⟩
```

## source-ClassifierAtoms-subtreeMeter.txt

```text
ClassifierAtoms.lean:6: def subtreeMeter : Tree→RMAF.Vertex→Measured (Option Tree)
ClassifierAtoms.lean:7:  | T,[]=>⟨some T,1⟩
ClassifierAtoms.lean:8:  | .leaf _,_::_=>⟨none,1⟩
ClassifierAtoms.lean:9:  | .node l r,s::p=>let m:=subtreeMeter (if s then r else l) p;⟨m.value,m.work+2⟩
```

## source-ClassifierRequestMeter-checkFee.txt

```text
ClassifierRequestMeter.lean:20: def checkFee (r : CheckRequest) : Nat := (requestMeter r).work
```

## source-ClassifierRequestMeter-requestMeter.txt

```text
ClassifierRequestMeter.lean:9: def requestMeter : CheckRequest→CheckReceipt Bool
ClassifierRequestMeter.lean:10:  | r@(.embedding T P)=>let m:=meterPairwise T P;⟨m.value,m.work+2,[r]⟩
ClassifierRequestMeter.lean:11:  | r@(.restriction T S B)=>let m:=meterRestrictionAgrees T S B;⟨m.value,m.work+2,[r]⟩
```

## source-ClosedPayload-cells.txt

```text
ClosedPayload.lean:10: def cells (F : Forest) : Nat := F.length+F.flatten.length
```

## source-ColorDP-Paint.txt

```text
ColorDP.lean:10: inductive Paint where
ColorDP.lean:11:   | leaf : Nat → Nat → Paint
ColorDP.lean:12:   | node : Nat → Paint → Paint → Paint
ColorDP.lean:13:   deriving DecidableEq, Repr
```

## source-ColorDP-delta_root.txt

```text
ColorDP.lean:15: def root : Paint → Nat
ColorDP.lean:16:   | .leaf _ c => c
ColorDP.lean:17:   | .node c _ _ => c

ColorDP.lean:23: def delta (a b : Nat) : Nat := if a == b then 0 else 1
```

## source-CommonConstructionWork-commonFreshMeter_contractMeter_expandBlockMeter.txt

```text
CommonConstructionWork.lean:15: def commonFreshMeter (T : Tree) : Charged Nat :=
CommonConstructionWork.lean:16:  let a:=meterLeaves T;let b:=labelMaxMeter a.value;⟨b.value+1,a.work+b.work+4⟩

CommonConstructionWork.lean:38: def contractMeter (a b z : Nat) : Tree→Charged Tree
CommonConstructionWork.lean:39:  | .leaf x=>⟨.leaf x,2⟩
CommonConstructionWork.lean:40:  | .node l r=>
CommonConstructionWork.lean:41:   let la:=leafEqualMeter l a;let rb:=leafEqualMeter r b
CommonConstructionWork.lean:42:   let lb:=leafEqualMeter l b;let ra:=leafEqualMeter r a
CommonConstructionWork.lean:43:   if (la.value&&rb.value)||(lb.value&&ra.value) then ⟨.leaf z,24⟩
CommonConstructionWork.lean:44:   else let x:=contractMeter a b z l;let y:=contractMeter a b z r
CommonConstructionWork.lean:45:        ⟨.node x.value y.value,x.work+y.work+24⟩

CommonConstructionWork.lean:76: def expandBlockMeter (a b z : Nat) : List Nat→Charged (List Nat)
CommonConstructionWork.lean:77:  | []=>⟨[],1⟩
CommonConstructionWork.lean:78:  | x::xs=>
CommonConstructionWork.lean:79:   let r:=expandBlockMeter a b z xs
CommonConstructionWork.lean:80:   ⟨(if x==z then [a,b] else [x])++r.value,r.work+12⟩
```

## source-CommonConstructionWork-commonPairMeter_expandCommonMeter.txt

```text
CommonConstructionWork.lean:57: def commonPairMeter (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) : Charged (Tree×Tree) :=
CommonConstructionWork.lean:58:  let p:=FastOrdinary.Oriented reverse T S
CommonConstructionWork.lean:59:  let z:=commonFreshMeter p.1;let t:=contractMeter c.a c.b z.value p.1;let s:=contractMeter c.a c.b z.value p.2
CommonConstructionWork.lean:60:  ⟨(t.value,s.value),z.work+t.work+s.work+8⟩

CommonConstructionWork.lean:88: def expandCommonMeter (T S : Tree) (reverse : Bool) (c : CherryBranching.Candidate) (F : List (List Nat)) : Charged (List (List Nat)) :=
CommonConstructionWork.lean:89:  let z:=commonFreshMeter (FastOrdinary.Oriented reverse T S).1
CommonConstructionWork.lean:90:  let r:=meterMap (expandBlockMeter c.a c.b z.value) F
CommonConstructionWork.lean:91:  ⟨r.value,z.work+r.work+4⟩
```

## source-CommonConstructionWork-labelMaxMeter_leafEqualMeter.txt

```text
CommonConstructionWork.lean:6: def labelMaxMeter : List Nat→Charged Nat
CommonConstructionWork.lean:7:  | []=>⟨0,1⟩
CommonConstructionWork.lean:8:  | x::xs=>let r:=labelMaxMeter xs;⟨Nat.max x r.value,r.work+4⟩

CommonConstructionWork.lean:32: def leafEqualMeter (T : Tree) (a : Nat) : Charged Bool :=
CommonConstructionWork.lean:33:  ⟨match T with | .leaf x=>x==a | .node _ _=>false,4⟩
```

## source-CommonExecutionBinding-commonMeter.txt

```text
CommonExecutionBinding.lean:38: def commonMeter (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : CommonReceipt (Option Forest) :=
CommonExecutionBinding.lean:39:  let setup:=commonSetupMeter T S a b d
CommonExecutionBinding.lean:40:  match setup.value with
CommonExecutionBinding.lean:41:  | none=>⟨none,setup.work+2,0,[]⟩
CommonExecutionBinding.lean:42:  | some built=>
CommonExecutionBinding.lean:43:    let r:=guardedMeter cb W built q
CommonExecutionBinding.lean:44:    ⟨r.value.join,setup.work+r.localWork+3,r.recursiveWork,r.calls⟩
```

## source-CommonGuardedSource-guardedMeter.txt

```text
CommonGuardedSource.lean:43: def guardedMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) : CommonReceipt (Option (Option Forest)) :=
CommonGuardedSource.lean:44:  let pre:=meterPretest d.ty d.sy
CommonGuardedSource.lean:45:  match pre.value with
CommonGuardedSource.lean:46:  | .found (some p)=>
CommonGuardedSource.lean:47:    let fy:=meterForest d.sy (some p)
CommonGuardedSource.lean:48:    let r:=withOutsideMeter cb W d q fy.value
CommonGuardedSource.lean:49:    ⟨some r.value,pre.work+fy.work+r.localWork+3,r.recursiveWork,r.calls⟩
CommonGuardedSource.lean:50:  | _=>⟨none,pre.work+2,0,[]⟩
```

## source-CommonGuardedSource-withOutsideMeter.txt

```text
CommonGuardedSource.lean:17: def withOutsideMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) : CommonReceipt (Option Forest) :=
CommonGuardedSource.lean:18:  let out:=outsideReplyMeter d FY
CommonGuardedSource.lean:19:  match out.value with
CommonGuardedSource.lean:20:  | none=>⟨none,out.work+2,0,[]⟩
CommonGuardedSource.lean:21:  | some FN=>let r:=runPaidMeter cb W d q FY FN
CommonGuardedSource.lean:22:             ⟨r.value,out.work+r.localWork+2,r.recursiveWork,r.calls⟩
```

## source-CommonLocalBinding-reconstructMeter.txt

```text
CommonLocalBinding.lean:57: def reconstructMeter (check : Forest→Measured Bool) (d : Setup) (FX FY FM FN : Forest) : Measured (Option Forest) :=
CommonLocalBinding.lean:58:  let guards:=FX.length+FY.length+FM.length+FN.length+4
CommonLocalBinding.lean:59:  if FM.length-1=FX.length-1 ∧ FN.length-1=FY.length-1 then
CommonLocalBinding.lean:60:   let m:=pickMeter check d.X d.Y d.x d.y d.rho d.gamma FM FN
CommonLocalBinding.lean:61:   ⟨m.value,guards+m.work⟩
CommonLocalBinding.lean:62:  else ⟨some (FX++FY),guards+FX.length+1⟩
```

## source-CommonOutsideSource-outsideExtensionMeter.txt

```text
CommonOutsideSource.lean:44: def outsideExtensionMeter (d : Setup) (FY : List (List Nat)) : Charged (List (List Nat)) :=
CommonOutsideSource.lean:45:  let r:=relabelForestMeter d.x d.gamma ([d.x]::FY);⟨r.value,r.work+2⟩
```

## source-CommonOutsideSource-outsideReplyMeter.txt

```text
CommonOutsideSource.lean:57: def outsideReplyMeter (d : Setup) (FY : List (List Nat)) : Charged (Option (List (List Nat))) :=
CommonOutsideSource.lean:58:  let pre:=meterPretest d.myT d.myS
CommonOutsideSource.lean:59:  match pre.value with
CommonOutsideSource.lean:60:  | .found c=>let r:=meterForest d.myS c;⟨some r.value,pre.work+r.work+3⟩
CommonOutsideSource.lean:61:  | .rejected=>let r:=outsideExtensionMeter d FY;⟨some r.value,pre.work+r.work+3⟩
CommonOutsideSource.lean:62:  | .refused=>⟨none,pre.work+2⟩
```

## source-CommonOutsideSource-relabelBlockMeter.txt

```text
CommonOutsideSource.lean:21: def relabelBlockMeter (a b : Nat) : List Nat→Charged (List Nat)
CommonOutsideSource.lean:22:  | []=>⟨[],1⟩
CommonOutsideSource.lean:23:  | x::xs=>let r:=relabelBlockMeter a b xs;⟨swap a b x::r.value,r.work+5⟩
```

## source-CommonOutsideSource-relabelForestMeter.txt

```text
CommonOutsideSource.lean:31: def relabelForestMeter (a b : Nat) : List (List Nat)→Charged (List (List Nat))
CommonOutsideSource.lean:32:  | []=>⟨[],1⟩
CommonOutsideSource.lean:33:  | B::F=>let x:=relabelBlockMeter a b B;let r:=relabelForestMeter a b F
CommonOutsideSource.lean:34:            ⟨x.value::r.value,x.work+r.work+2⟩
```

## source-CommonPaidSource-CommonReceipt.txt

```text
CommonPaidSource.lean:11: structure CommonReceipt (α : Type) where
CommonPaidSource.lean:12:  value : α
CommonPaidSource.lean:13:  localWork : Nat
CommonPaidSource.lean:14:  recursiveWork : Nat
CommonPaidSource.lean:15:  calls : List Job
```

## source-CommonPaidSource-jobsAnswersMeter_paidJobsMeter.txt

```text
CommonPaidSource.lean:18: def paidJobsMeter (d : Setup) (q : Nat) : Charged (List Job) :=
CommonPaidSource.lean:19:  if q=0 then ⟨[],2⟩ else ⟨[⟨d.tx,d.sx,q-1⟩,⟨d.mxT,d.mxS,q-1⟩],12⟩

CommonPaidSource.lean:27: def jobsAnswersMeter (cb : Ordinary) (W : OrdinaryWork) : List Job→CommonReceipt (List (Option Forest))
CommonPaidSource.lean:28:  | []=>⟨[],1,0,[]⟩
CommonPaidSource.lean:29:  | j::js=>let a:=cb j.T j.S j.budget;let r:=jobsAnswersMeter cb W js
CommonPaidSource.lean:30:            ⟨a::r.value,r.localWork+3,W j.T j.S j.budget+r.recursiveWork,j::r.calls⟩
```

## source-CommonPaidSource-runPaidMeter.txt

```text
CommonPaidSource.lean:49: def runPaidMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) : CommonReceipt (Option Forest) :=
CommonPaidSource.lean:50:  let js:=paidJobsMeter d q;let asw:=jobsAnswersMeter cb W js.value
CommonPaidSource.lean:51:  let finish : Charged (Option Forest):=
CommonPaidSource.lean:52:   match asw.value with
CommonPaidSource.lean:53:   | [some FX,some FM]=>
CommonPaidSource.lean:54:     let r:=Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN
CommonPaidSource.lean:55:     match r.value with
CommonPaidSource.lean:56:     | none=>⟨none,r.work+2⟩
CommonPaidSource.lean:57:     | some G=>⟨if G.length-1≤q then some G else none,r.work+G.length+4⟩
CommonPaidSource.lean:58:   | _=>⟨none,2⟩
CommonPaidSource.lean:59:  ⟨finish.value,js.work+asw.localWork+finish.work+2,asw.recursiveWork,asw.calls⟩
```

## source-CommonSetupBinding-commonSetupMeter.txt

```text
CommonSetupBinding.lean:8: def commonSetupMeter (T S : Tree) (a b : Nat) (d : BadSelection) : Measured (Option Setup) :=
CommonSetupBinding.lean:9:  let x:=subtreeLabelsMeter S d.badArc;let c:=coreMeter S a b
CommonSetupBinding.lean:10:  let y:=c.value++[d.c];let r:=setupMeter T S x.value y d.badArc
CommonSetupBinding.lean:11:  ⟨r.value,x.work+c.work+c.value.length+r.work+3⟩
```

## source-CommonSourceDebit-commonSource.txt

```text
CommonSourceDebit.lean:28: def commonSource (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : Charged (Option Forest) :=
CommonSourceDebit.lean:29:  let r:=commonMeter cb W T S a b d q;⟨r.value,r.localWork+r.recursiveWork⟩
```

## source-CompleteNamedSources-paidCaseCompleteSource.txt

```text
CompleteNamedSources.lean:46: def paidCaseCompleteSource (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
CompleteNamedSources.lean:47:  (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : SourceExecution :=
CompleteNamedSources.lean:48:  let p:=paidOuterMeter T S c out
CompleteNamedSources.lean:49:  let r:=selectedPaidSource actual W T S c q out p.value
CompleteNamedSources.lean:50:  ⟨r.value,p.work+r.work⟩
```

## source-CompleteNamedSources-selectedPaidSource.txt

```text
CompleteNamedSources.lean:20: def selectedPaidSource (actual : GenericForest.FrontierWork.Ordinary) (W : GenericForest.FrontierWork.OrdinaryWork)
CompleteNamedSources.lean:21:  (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : PaidRoute→SourceExecution
CompleteNamedSources.lean:22:  | .empty=>⟨⟨none,[]⟩,0⟩
CompleteNamedSources.lean:23:  | .good X Y Z=>goodPairSource actual W T S X Y Z q
CompleteNamedSources.lean:24:  | .hard=>hardPaidSource actual W T S q c out
CompleteNamedSources.lean:25:  | .bad X Y Z edge=>badPairSource actual W T S X Y Z edge q
```

## source-ConcreteFees-source.txt

```text
ConcreteFees.lean:10: def source (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b q : Nat) : Charged Rule5OrdinaryDispatch.Result :=
ConcreteFees.lean:11:  dispatchSource cb W checkFee (literalFee T S a b) T S a b q
```

## source-CoreGraph-CherryAt_LeafAt_subtree.txt

```text
CoreGraph.lean:10: def subtree : Tree → Vertex → Option Tree
CoreGraph.lean:11:   | t, [] => some t
CoreGraph.lean:12:   | .leaf _, _ :: _ => none
CoreGraph.lean:13:   | .node l r, b :: v => subtree (if b then r else l) v

CoreGraph.lean:17: def LeafAt (t : Tree) (v : Vertex) (x : Nat) : Prop :=
CoreGraph.lean:18:   subtree t v = some (.leaf x)

CoreGraph.lean:20: def CherryAt (t : Tree) (p : Vertex) (x y : Nat) : Prop :=
CoreGraph.lean:21:   subtree t p = some (.node (.leaf x) (.leaf y))
```

## source-CoreProgram-Choice_GTree_Group_Output_Receipt_combine_prefixRoot.txt

```text
CoreProgram.lean:10: structure Group where
CoreProgram.lean:11:   origin : Vertex
CoreProgram.lean:12:   labels : List Nat
CoreProgram.lean:13:   color : Nat
CoreProgram.lean:14:   deriving DecidableEq, Repr

CoreProgram.lean:16: inductive GTree where
CoreProgram.lean:17:   | leaf : Group → GTree
CoreProgram.lean:18:   | node : Vertex → GTree → GTree → GTree
CoreProgram.lean:19:   deriving DecidableEq, Repr

CoreProgram.lean:53: inductive Choice where
CoreProgram.lean:54:   | finish
CoreProgram.lean:55:   | one : Group → Choice
CoreProgram.lean:56:   | two : Group → Group → Choice
CoreProgram.lean:57:   | refuse : String → Choice
CoreProgram.lean:58:   deriving Repr

CoreProgram.lean:76: structure Output where
CoreProgram.lean:77:   partition : List (List Nat)
CoreProgram.lean:78:                                                                              
CoreProgram.lean:79:                                                                 
CoreProgram.lean:80:   sourceCuts : List Vertex
CoreProgram.lean:81:   deriving DecidableEq, Repr

CoreProgram.lean:83: structure Receipt where
CoreProgram.lean:84:   outputs : List Output := []
CoreProgram.lean:85:   refusals : List String := []
CoreProgram.lean:86:   visited : Nat := 0
CoreProgram.lean:87:   childAttempts : Nat := 0
CoreProgram.lean:88:   pruned : Nat := 0
CoreProgram.lean:89:   deriving Repr

CoreProgram.lean:91: def combine (a b : Receipt) : Receipt :=
CoreProgram.lean:92:   ⟨a.outputs ++ b.outputs, a.refusals ++ b.refusals,
CoreProgram.lean:93:     a.visited + b.visited, a.childAttempts + b.childAttempts, a.pruned + b.pruned⟩

CoreProgram.lean:95: def prefixRoot (r : Receipt) : Receipt := { r with visited := r.visited + 1 }
```

## source-CoreProgram-attempt_choose_erase_fromTree_groups_mixedCherry_normalize_run_step.txt

```text
CoreProgram.lean:21: def fromTree (color : Nat → Nat) (p : Vertex) : Tree → GTree
CoreProgram.lean:22:   | .leaf x => .leaf ⟨p, [x], color x⟩
CoreProgram.lean:23:   | .node l r => .node p (fromTree color (p ++ [false]) l) (fromTree color (p ++ [true]) r)

CoreProgram.lean:25: def groups : GTree → List Group
CoreProgram.lean:26:   | .leaf g => [g]
CoreProgram.lean:27:   | .node _ l r => groups l ++ groups r

CoreProgram.lean:29: def normalize : GTree → GTree
CoreProgram.lean:30:   | .leaf g => .leaf g
CoreProgram.lean:31:   | .node p l r =>
CoreProgram.lean:32:       match normalize l, normalize r with
CoreProgram.lean:33:       | .leaf a, .leaf b =>
CoreProgram.lean:34:           if a.color = b.color then .leaf ⟨p, a.labels ++ b.labels, a.color⟩
CoreProgram.lean:35:           else .node p (.leaf a) (.leaf b)
CoreProgram.lean:36:       | a, b => .node p a b

CoreProgram.lean:38: def erase (chosen : Vertex) : GTree → Option GTree
CoreProgram.lean:39:   | .leaf g => if g.origin = chosen then none else some (.leaf g)
CoreProgram.lean:40:   | .node p l r =>
CoreProgram.lean:41:       if p = chosen then none else
CoreProgram.lean:42:       match erase chosen l, erase chosen r with
CoreProgram.lean:43:       | none, none => none
CoreProgram.lean:44:       | some a, none => some a
CoreProgram.lean:45:       | none, some b => some b
CoreProgram.lean:46:       | some a, some b => some (.node p a b)

CoreProgram.lean:48: def mixedCherry : GTree → Option (Group × Group)
CoreProgram.lean:49:   | .leaf _ => none
CoreProgram.lean:50:   | .node _ (.leaf a) (.leaf b) => some (a, b)
CoreProgram.lean:51:   | .node _ l r => (mixedCherry l).or (mixedCherry r)

CoreProgram.lean:60: def choose (t : GTree) : Choice :=
CoreProgram.lean:61:   let gs := groups t
CoreProgram.lean:62:   match gs with
CoreProgram.lean:63:   | [] => .refuse "empty current source"
CoreProgram.lean:64:   | first :: _ =>
CoreProgram.lean:65:       if gs.all (fun g => g.color == first.color) then .finish
CoreProgram.lean:66:       else
CoreProgram.lean:67:         match gs.find? (fun g => (gs.filter (fun h => h.color == g.color)).length == 1) with
CoreProgram.lean:68:         | some g => .one g
CoreProgram.lean:69:         | none =>
CoreProgram.lean:70:             match mixedCherry t with
CoreProgram.lean:71:             | some (a, b) =>
CoreProgram.lean:72:                 if a.color == b.color then .refuse "unnormalized homogeneous cherry"
CoreProgram.lean:73:                 else .two a b
CoreProgram.lean:74:             | none => .refuse "no mixed cherry in multicolor source"

CoreProgram.lean:97: def attempt (continuation : GTree → List Group → List Vertex → Receipt)
CoreProgram.lean:98:     (t : GTree) (detached : List Group) (cuts : List Vertex) (g : Group) : Receipt :=
CoreProgram.lean:99:   if g.origin = [] then ⟨[], ["attempt to cut original root"], 0, 1, 0⟩
CoreProgram.lean:100:   else if cuts.contains g.origin then ⟨[], ["duplicate original source cut"], 0, 1, 0⟩
CoreProgram.lean:101:   else
CoreProgram.lean:102:     match erase g.origin t with
CoreProgram.lean:103:     | none => ⟨[], ["attempt removed entire current source"], 0, 1, 0⟩
CoreProgram.lean:104:     | some next =>
CoreProgram.lean:105:         let r := continuation next (g :: detached) (g.origin :: cuts)
CoreProgram.lean:106:         { r with childAttempts := r.childAttempts + 1 }

CoreProgram.lean:108: def step (continuation : GTree → List Group → List Vertex → Receipt)
CoreProgram.lean:109:     (current : GTree) (detached : List Group) (cuts : List Vertex) : Receipt :=
CoreProgram.lean:110:   let t := normalize current
CoreProgram.lean:111:   match choose t with
CoreProgram.lean:112:   | .finish => ⟨[⟨detached.map Group.labels ++ [(groups t).flatMap Group.labels], cuts⟩], [], 1, 0, 0⟩
CoreProgram.lean:113:   | .one g => prefixRoot (attempt continuation t detached cuts g)
CoreProgram.lean:114:   | .two a b => prefixRoot (combine (attempt continuation t detached cuts a)
CoreProgram.lean:115:       (attempt continuation t detached cuts b))
CoreProgram.lean:116:   | .refuse why => ⟨[], [why], 1, 0, 0⟩

CoreProgram.lean:120: def run : Nat → GTree → List Group → List Vertex → Receipt
CoreProgram.lean:121:   | 0 => step (fun _ _ _ => ⟨[], [], 0, 0, 1⟩)
CoreProgram.lean:122:   | q + 1 => step (run q)
```

## source-CoreProgram-generate.txt

```text
CoreProgram.lean:124: def generate (t : Tree) (color : Nat → Nat) (budget : Nat) : Receipt :=
CoreProgram.lean:125:   if (leaves t).Nodup then run (min budget ((leaves t).length - 1)) (fromTree color [] t) [] []
CoreProgram.lean:126:   else ⟨[], ["duplicate original label"], 0, 0, 0⟩
```

## source-CurrentQuery-CurrentResult_CurrentResult.answer?.txt

```text
CurrentQuery.lean:8: inductive CurrentResult where
CurrentQuery.lean:9:  | malformed
CurrentQuery.lean:10:  | answered (answer : Option Forest)
CurrentQuery.lean:11:  deriving DecidableEq, Repr

CurrentQuery.lean:21: def CurrentResult.answer? : CurrentResult → Option Forest
CurrentQuery.lean:22:  | .malformed => none
CurrentQuery.lean:23:  | .answered answer => answer
```

## source-DisjointParentSource-disjointQueryLocalSource.txt

```text
DisjointParentSource.lean:10: def disjointQueryLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
DisjointParentSource.lean:11:  (parts : List (List Nat)) (q : Nat) : SourceExecution:=
DisjointParentSource.lean:12:  let paid:=parts.length-1
DisjointParentSource.lean:13:  if paid≤q then
DisjointParentSource.lean:14:   let r:=ordinaryLocalSource actual T S parts (q-paid)
DisjointParentSource.lean:15:   let check:=checkedMeter T S q r.value.answer
DisjointParentSource.lean:16:   ⟨⟨check.value,r.value.calls⟩,parts.length+r.work+check.work+16⟩
DisjointParentSource.lean:17:  else ⟨⟨none,[]⟩,parts.length+8⟩
```

## source-DisjointParentSource-disjointQuerySource.txt

```text
DisjointParentSource.lean:26: def disjointQuerySource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
DisjointParentSource.lean:27:  (T S : Tree) (parts : List (List Nat)) (q : Nat) : SourceExecution:=
DisjointParentSource.lean:28:  let r:=disjointQueryLocalSource actual T S parts q
DisjointParentSource.lean:29:  ⟨r.value,r.work+callsForestDebit actual W r.value.calls⟩
```

## source-DisjointParentSource-disjointRunSource.txt

```text
DisjointParentSource.lean:46: def disjointRunSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
DisjointParentSource.lean:47:  (T S : Tree) (a b q : Nat) : Charged (Option (List (List Nat))):=
DisjointParentSource.lean:48:  let x:=singletonChildMeter S a;let y:=singletonChildMeter S b
DisjointParentSource.lean:49:  let cs:=runChildrenSource actual W T S q [x.value,y.value]
DisjointParentSource.lean:50:  let p:=Rule5PendantLocalWork.partitionMeter S a b
DisjointParentSource.lean:51:  let qr:=disjointQuerySource actual W T S p.value q
DisjointParentSource.lean:52:  let best:=chooseMeter cs.value qr.value.answer
DisjointParentSource.lean:53:  ⟨best.value,x.work+y.work+cs.work+p.work+qr.work+best.work+12⟩
```

## source-Dispatcher-Call_Execution.txt

```text
Dispatcher.lean:10: structure Call where
Dispatcher.lean:11:   target : Option Tree
Dispatcher.lean:12:   sources : List Tree
Dispatcher.lean:13:   budget : Nat

Dispatcher.lean:15: structure Execution where
Dispatcher.lean:16:   answer : Option Forest
Dispatcher.lean:17:   calls : List Call
```

## source-ELCherry-meterCherries.txt

```text
ELCherry.lean:5: def meterCherries : Tree→Charged (List (RMAF.Vertex×Nat×Nat))
ELCherry.lean:6:  | .leaf _=>⟨[],2⟩
ELCherry.lean:7:  | .node l r=>let a:=meterCherries l;let b:=meterCherries r
ELCherry.lean:8:   ⟨match l,r with
ELCherry.lean:9:    | .leaf x,.leaf y=>[([],x,y)]
ELCherry.lean:10:    | _,_=>a.value.map (fun (p,x,y)=>(false::p,x,y))++b.value.map (fun (p,x,y)=>(true::p,x,y)),
ELCherry.lean:11:    a.work+b.work+8*(a.value.length+b.value.length+1)+4⟩
```

## source-ELCherry-meterCherryCandidates.txt

```text
ELCherry.lean:31: def meterCherryCandidates (T S : Tree) : Charged (List Candidate) :=
ELCherry.lean:32:  let c:=meterCherries T
ELCherry.lean:33:  let m:=meterMap (fun (p,a,b)=>let cuts:=meterPendant S a b;⟨(⟨p,a,b,cuts.value⟩:Candidate),cuts.work+4⟩) c.value
ELCherry.lean:34:  ⟨m.value,c.work+m.work+2⟩
```

## source-ELCherry-meterSelect.txt

```text
ELCherry.lean:69: def meterSelect (T S : Tree) : Charged (Option (Priority×Candidate)) :=
ELCherry.lean:70:  let c:=meterCherryCandidates T S
ELCherry.lean:71:  let common:=meterFind (fun x:Candidate=>⟨x.originalCuts.isEmpty,1⟩) c.value
ELCherry.lean:72:  let one:=meterFind (fun x:Candidate=>⟨x.originalCuts.length==1,4*(x.originalCuts.length+1)⟩) c.value
ELCherry.lean:73:  let high:=meterFind (fun x:Candidate=>⟨decide (3≤x.originalCuts.length),4*(x.originalCuts.length+1)⟩) c.value
ELCherry.lean:74:  ⟨match common.value with
ELCherry.lean:75:   | some x=>some (.common,x)
ELCherry.lean:76:   | none=>match one.value with
ELCherry.lean:77:     | some x=>some (.one,x)
ELCherry.lean:78:     | none=>match high.value with
ELCherry.lean:79:       | some x=>some (.high,x)
ELCherry.lean:80:       | none=>c.value.head?.map (fun x=>(.hard2,x)),
ELCherry.lean:81:   c.work+common.work+one.work+high.work+8⟩
```

## source-ELEarly-ChoiceMeasured.txt

```text
ELEarly.lean:10: structure ChoiceMeasured (T S : Tree) where
ELEarly.lean:11:  value : Option (Rule4.Choice T S)
ELEarly.lean:12:  work : Nat
ELEarly.lean:13:  checks : List (Rule4.RawChoice×Bool)
```

## source-ELGeometry-meterDropLast.txt

```text
ELGeometry.lean:101: def meterDropLast : RMAF.Vertex→Charged RMAF.Vertex
ELGeometry.lean:102:  | []=>⟨[],1⟩ | [_]=>⟨[],2⟩
ELGeometry.lean:103:  | x::y::xs=>let r:=meterDropLast (y::xs);⟨x::r.value,r.work+4⟩
```

## source-ELGeometry-meterEdges_meterSubtreeLabels.txt

```text
ELGeometry.lean:35: def meterEdges (T : Tree) : Charged (List RMAF.Vertex) :=
ELGeometry.lean:36:  let v:=meterVertices T;⟨v.value.tail,v.work+4⟩

ELGeometry.lean:70: def meterSubtreeLabels (T : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
ELGeometry.lean:71:  let a:=meterSubtree T v
ELGeometry.lean:72:  match a.value with
ELGeometry.lean:73:  | none=>⟨[],a.work+2⟩
ELGeometry.lean:74:  | some U=>let b:=meterLeaves U;⟨b.value,a.work+b.work+2⟩
```

## source-ELGeometry-meterPendantCheck.txt

```text
ELGeometry.lean:122: def meterPendantCheck (S : Tree) (a b : Nat) (v : RMAF.Vertex) : Charged Bool :=
ELGeometry.lean:123:  let d:=meterDropLast v
ELGeometry.lean:124:  let m:=meterMinimal [a,b] S;let c:=meterVertexContains d.value m.value
ELGeometry.lean:125:  let n:=meterMinimal [a,b] S;let e:=meterVertexContains v n.value
ELGeometry.lean:126:  ⟨!v.isEmpty&&c.value&&(!e.value),d.work+m.work+c.work+n.work+e.work+4⟩
```

## source-ELGeometry-meterPendant_meterSubtree_meterVertices.txt

```text
ELGeometry.lean:5: def meterVertices : Tree→Charged (List RMAF.Vertex)
ELGeometry.lean:6:  | .leaf _=>⟨[[]],4⟩
ELGeometry.lean:7:  | .node l r=>let a:=meterVertices l;let b:=meterVertices r
ELGeometry.lean:8:    ⟨[]::(a.value.map (false::·)++b.value.map (true::·)),a.work+b.work+8*(a.value.length+b.value.length+1)⟩

ELGeometry.lean:43: def meterSubtree : Tree→RMAF.Vertex→Charged (Option Tree)
ELGeometry.lean:44:  | T,[]=>⟨some T,2⟩
ELGeometry.lean:45:  | .leaf _,_::_=>⟨none,2⟩
ELGeometry.lean:46:  | .node l r,s::v=>let a:=meterSubtree (if s then r else l) v;⟨a.value,a.work+4⟩

ELGeometry.lean:146: def meterPendant (S : Tree) (a b : Nat) : Charged (List RMAF.Vertex) :=
ELGeometry.lean:147:  let v:=meterVertices S;let f:=meterFilter (meterPendantCheck S a b) v.value
ELGeometry.lean:148:  ⟨f.value,v.work+f.work+2⟩
```

## source-ELOuter-Front.txt

```text
ELOuter.lean:5: inductive Front (T S : Tree) where
ELOuter.lean:6:  | stop (answer : Option CommonForest)
ELOuter.lean:7:  | selected (early : FastOrdinary.Early T S)
```

## source-ELPretest-BestMeasured.txt

```text
ELPretest.lean:86: structure BestMeasured (α : Type) where
ELPretest.lean:87:  value : Option α
ELPretest.lean:88:  work : Nat
ELPretest.lean:89:  checks : List (α×Bool)
ELPretest.lean:90:  tailSizes : List Nat
ELPretest.lean:91:  comparisons : List (Nat×Nat)
ELPretest.lean:92:  deriving Repr
```

## source-ELPrimitives-meterFilter_meterMap.txt

```text
ELPrimitives.lean:7: def meterMap {α β : Type} (f : α→Charged β) : List α→Charged (List β)
ELPrimitives.lean:8:  | []=>⟨[],1⟩
ELPrimitives.lean:9:  | x::xs=>let a:=f x;let r:=meterMap f xs;⟨a.value::r.value,a.work+r.work+4⟩

ELPrimitives.lean:20: def meterFilter {α : Type} (f : α→Charged Bool) : List α→Charged (List α)
ELPrimitives.lean:21:  | []=>⟨[],1⟩
ELPrimitives.lean:22:  | x::xs=>let a:=f x;let r:=meterFilter f xs;⟨if a.value then x::r.value else r.value,a.work+r.work+4⟩
```

## source-ELPrimitives-meterFind.txt

```text
ELPrimitives.lean:33: def meterFind {α : Type} (f : α→Charged Bool) : List α→Charged (Option α)
ELPrimitives.lean:34:  | []=>⟨none,1⟩
ELPrimitives.lean:35:  | x::xs=>let a:=f x;if a.value then ⟨some x,a.work+4⟩
ELPrimitives.lean:36:    else let r:=meterFind f xs;⟨r.value,a.work+r.work+4⟩
```

## source-ELRule4Guards-meterLocalGuard_meterRule4Priority.txt

```text
ELRule4Guards.lean:30: def meterRule4Priority (T S : Tree) : Charged Bool :=
ELRule4Guards.lean:31:  let p:=meterOrdinaryProper T S;let c:=meterNoCommon T S
ELRule4Guards.lean:32:  let a:=meterNoOne T S;let b:=meterNoOne S T
ELRule4Guards.lean:33:  ⟨p.value&&c.value&&a.value&&b.value,p.work+c.work+a.work+b.work+8⟩

ELRule4Guards.lean:82: def meterLocalGuard (T S : Tree) (raw : Rule4.RawChoice) : Charged Bool :=
ELRule4Guards.lean:83:  let t:=meterOrderedCherries T;let ta:=meterPairContains (raw.a,raw.b) t.value
ELRule4Guards.lean:84:  let s:=meterOrderedCherries S;let sa:=meterPairContains (raw.a,raw.c) s.value
ELRule4Guards.lean:85:  let p:=meterPendant S raw.a raw.b;let perm:=meterVertexPerm p.value [raw.cHead,raw.xHead]
ELRule4Guards.lean:86:  let lab:=meterSubtreeLabels S raw.cHead;let equal:=meterNatListEq lab.value [raw.c]
ELRule4Guards.lean:87:  ⟨ta.value&&sa.value&&(raw.a !=raw.b)&&perm.value&&equal.value,
ELRule4Guards.lean:88:   t.work+ta.work+s.work+sa.work+p.work+perm.work+lab.work+equal.work+16⟩
```

## source-ELRule4Guards-meterNoCommon_meterNoOne.txt

```text
ELRule4Guards.lean:14: def meterNoCommon (T S : Tree) : Charged Bool :=
ELRule4Guards.lean:15:  let t:=meterOrderedCherries T
ELRule4Guards.lean:16:  let a:=meterAll (fun ab=>let s:=meterOrderedCherries S;let m:=meterPairContains ab s.value
ELRule4Guards.lean:17:    ⟨!m.value,s.work+m.work+2⟩) t.value
ELRule4Guards.lean:18:  ⟨a.value,t.work+a.work+2⟩

ELRule4Guards.lean:22: def meterNoOne (T S : Tree) : Charged Bool :=
ELRule4Guards.lean:23:  let t:=meterOrderedCherries T
ELRule4Guards.lean:24:  let a:=meterAll (fun ab=>let p:=meterPendant S ab.1 ab.2
ELRule4Guards.lean:25:    ⟨p.value.length !=1,p.work+4*(p.value.length+1)+2⟩) t.value
ELRule4Guards.lean:26:  ⟨a.value,t.work+a.work+2⟩
```

## source-ELRule4Primitives-meterNatListEq_meterOrderedCherries_meterPairContains_meterVertexPerm.txt

```text
ELRule4Primitives.lean:5: def meterPairContains (x : Nat×Nat) : List (Nat×Nat)→Charged Bool
ELRule4Primitives.lean:6:  | []=>⟨false,1⟩
ELRule4Primitives.lean:7:  | y::ys=>if x.1==y.1 && x.2==y.2 then ⟨true,8⟩ else let r:=meterPairContains x ys;⟨r.value,r.work+8⟩

ELRule4Primitives.lean:22: def meterOrderedCherries : Tree→Charged (List (Nat×Nat))
ELRule4Primitives.lean:23:  | .leaf _=>⟨[],2⟩
ELRule4Primitives.lean:24:  | .node l r=>let a:=meterOrderedCherries l;let b:=meterOrderedCherries r
ELRule4Primitives.lean:25:   ⟨(match l,r with | .leaf x,.leaf y=>[(x,y),(y,x)] | _,_=>[])++a.value++b.value,
ELRule4Primitives.lean:26:    a.work+b.work+8*(a.value.length+b.value.length+3)⟩

ELRule4Primitives.lean:69: def meterVertexPerm : List RMAF.Vertex→List RMAF.Vertex→Charged Bool
ELRule4Primitives.lean:70:  | [],ys=>⟨ys.isEmpty,1⟩
ELRule4Primitives.lean:71:  | x::xs,ys=>let c:=meterVertexContains x ys;let e:=meterVertexErase x ys;let r:=meterVertexPerm xs e.value
ELRule4Primitives.lean:72:    ⟨c.value&&r.value,c.work+e.work+r.work+4⟩

ELRule4Primitives.lean:104: def meterNatListEq : List Nat→List Nat→Charged Bool
ELRule4Primitives.lean:105:  | [],[]=>⟨true,2⟩ | [],_::_=>⟨false,2⟩ | _::_,[]=>⟨false,2⟩
ELRule4Primitives.lean:106:  | x::xs,y::ys=>if x==y then let r:=meterNatListEq xs ys;⟨r.value,r.work+4⟩ else ⟨false,4⟩
```

## source-ELRule4Primitives-meterVertexErase.txt

```text
ELRule4Primitives.lean:47: def meterVertexErase (x : RMAF.Vertex) : List RMAF.Vertex→Charged (List RMAF.Vertex)
ELRule4Primitives.lean:48:  | []=>⟨[],1⟩
ELRule4Primitives.lean:49:  | y::ys=>let eq:=meterAddressEq x y
ELRule4Primitives.lean:50:    if eq.value then ⟨ys,eq.work+4⟩ else let r:=meterVertexErase x ys;⟨y::r.value,eq.work+r.work+4⟩
```

## source-ELRule4Raw-meterFlatMap.txt

```text
ELRule4Raw.lean:10: def meterFlatMap {α β : Type} (f : α→Charged (List β)) : List α→Charged (List β)
ELRule4Raw.lean:11:  | []=>⟨[],1⟩
ELRule4Raw.lean:12:  | x::xs=>let a:=f x;let r:=meterFlatMap f xs;⟨a.value++r.value,a.work+r.work+6*(a.value.length+1)⟩
```

## source-ELRule4Raw-meterRawAB.txt

```text
ELRule4Raw.lean:88: def meterRawAB (S : Tree) (ab : Nat×Nat) : Charged (List Rule4.RawChoice) :=
ELRule4Raw.lean:89:  let c:=meterOrderedCherries S;let m:=meterFlatMap (meterRawAC S ab) c.value
ELRule4Raw.lean:90:  ⟨m.value,c.work+m.work+2⟩
```

## source-ELRule4Raw-meterRawAC.txt

```text
ELRule4Raw.lean:40: def meterRawAC (S : Tree) (ab ac : Nat×Nat) : Charged (List Rule4.RawChoice) :=
ELRule4Raw.lean:41:  let test:=meterPendant S ab.1 ab.2
ELRule4Raw.lean:42:  if ab.1=ac.1 ∧ test.value.length=2 then
ELRule4Raw.lean:43:   let p:=meterPendant S ab.1 ab.2
ELRule4Raw.lean:44:   let f:=meterFlatMap (meterRawR S ab ac) p.value
ELRule4Raw.lean:45:   ⟨f.value,test.work+4*(test.value.length+1)+p.work+f.work+8⟩
ELRule4Raw.lean:46:  else ⟨[],test.work+4*(test.value.length+1)+4⟩
```

## source-ELRule4Raw-meterRawChoices.txt

```text
ELRule4Raw.lean:113: def meterRawChoices (T S : Tree) : Charged (List Rule4.RawChoice) :=
ELRule4Raw.lean:114:  let c:=meterOrderedCherries T;let m:=meterFlatMap (meterRawAB S) c.value
ELRule4Raw.lean:115:  ⟨m.value,c.work+m.work+2⟩
```

## source-ELRule4Raw-meterRawR.txt

```text
ELRule4Raw.lean:33: def meterRawR (S : Tree) (ab ac : Nat×Nat) (q : RMAF.Vertex) : Charged (List Rule4.RawChoice) :=
ELRule4Raw.lean:34:  let p:=meterPendant S ab.1 ab.2
ELRule4Raw.lean:35:  let m:=meterMap (fun r=>⟨(⟨ab.1,ab.2,ac.2,q,r⟩:Rule4.RawChoice),4⟩) p.value
ELRule4Raw.lean:36:  ⟨m.value,p.work+m.work+2⟩
```

## source-EarlySelector-Early.txt

```text
EarlySelector.lean:7: inductive Early (T S : Tree) where
EarlySelector.lean:8:  | common (reverse : Bool) (c : Candidate)
EarlySelector.lean:9:  | one (reverse : Bool) (c : Candidate)
EarlySelector.lean:10:  | high (reverse : Bool) (c : Candidate)
EarlySelector.lean:11:  | rule4Forward (s : Rule4.Choice T S)
EarlySelector.lean:12:  | rule4Reverse (s : Rule4.Choice S T)
EarlySelector.lean:13:  | hard2 (c d : Candidate)
EarlySelector.lean:14:  | refused
```

## source-Executable-pendantOriginal_subtreeLabels.txt

```text
Executable.lean:12: def pendantOriginal (S : Tree) (a b : Nat) : List Vertex :=
Executable.lean:13:   (vertices S).filter fun v => !v.isEmpty &&
Executable.lean:14:     (minimalVertices [a,b] S).contains v.dropLast &&
Executable.lean:15:     !(minimalVertices [a,b] S).contains v

Executable.lean:17: def subtreeLabels : Tree → Vertex → List Nat
Executable.lean:18:   | S, [] => leaves S
Executable.lean:19:   | .leaf _, _ :: _ => []
Executable.lean:20:   | .node l r, s :: v => subtreeLabels (if s then r else l) v
```

## source-Executable-vertices.txt

```text
Executable.lean:8: def vertices : Tree → List Vertex
Executable.lean:9:   | .leaf _ => [[]]
Executable.lean:10:   | .node l r => [] :: (prependSide false (vertices l) ++ prependSide true (vertices r))
```

## source-FinalClassifierWork-finalMeter.txt

```text
FinalClassifierWork.lean:103: def finalMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option FinalSelection) :=
FinalClassifierWork.lean:104:  let l:=localMeter fee T S a b
FinalClassifierWork.lean:105:  match l.value with
FinalClassifierWork.lean:106:  | none=>⟨none,l.work+1,l.calls⟩
FinalClassifierWork.lean:107:  | some .remaining=>let d:=selectBadMeter fee T S a b
FinalClassifierWork.lean:108:   match d.value with
FinalClassifierWork.lean:109:   | none=>⟨none,l.work+d.work+l.calls.length+2,l.calls++d.calls⟩
FinalClassifierWork.lean:110:   | some bad=>let x:=subtreeLabelsMeter S bad.badArc;let z:=boundaryMeter T x.value bad.c
FinalClassifierWork.lean:111:    ⟨z.value.map (.remaining bad),l.work+d.work+x.work+z.work+l.calls.length+4,l.calls++d.calls⟩
FinalClassifierWork.lean:112:  | some s=>⟨some (.prefix s),l.work+2,l.calls⟩
```

## source-FinalClassifierWork-localMeter.txt

```text
FinalClassifierWork.lean:16: def localMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option LocalSelection) :=
FinalClassifierWork.lean:17:  let ad:=admittedMeter fee T S a b
FinalClassifierWork.lean:18:  if ad.value then let r:=localTailMeter fee T S a b
FinalClassifierWork.lean:19:   ⟨r.value,ad.work+r.work+ad.calls.length+2,ad.calls++r.calls⟩
FinalClassifierWork.lean:20:  else ⟨none,ad.work+1,ad.calls⟩
```

## source-FinalClassifierWork-localTailMeter.txt

```text
FinalClassifierWork.lean:5: def localTailMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option LocalSelection) :=
FinalClassifierWork.lean:6:  let l:=selectLargeMeter fee T S a b
FinalClassifierWork.lean:7:  match l.value with
FinalClassifierWork.lean:8:  | some e=>⟨some (.large e),l.work+2,l.calls⟩
FinalClassifierWork.lean:9:  | none=>let t:=selectSizeTwoMeter fee T S a b
FinalClassifierWork.lean:10:   match t.value with
FinalClassifierWork.lean:11:   | some c=>⟨some (.two c),l.work+t.work+l.calls.length+3,l.calls++t.calls⟩
FinalClassifierWork.lean:12:   | none=>let o:=selectOutsideMeter fee T S a b
FinalClassifierWork.lean:13:    ⟨some (match o.value with | some c=>.outside c | none=>.remaining),
FinalClassifierWork.lean:14:     l.work+t.work+o.work+l.calls.length+t.calls.length+5,l.calls++(t.calls++o.calls)⟩
```

## source-FinalSelector-BadSelection_FinalSelection.txt

```text
FinalSelector.lean:5: structure BadSelection where
FinalSelector.lean:6:  badArc : RMAF.Vertex
FinalSelector.lean:7:  singletonArc : RMAF.Vertex
FinalSelector.lean:8:  c : Nat
FinalSelector.lean:9:  deriving Repr, DecidableEq

FinalSelector.lean:180: inductive FinalSelection where
FinalSelector.lean:181:  | prefix (s : LocalSelection)
FinalSelector.lean:182:  | remaining (d : BadSelection) (z : BoundarySelection)
FinalSelector.lean:183:  deriving Repr, DecidableEq
```

## source-FinalSelector-BoundarySelection.txt

```text
FinalSelector.lean:107: inductive BoundarySelection where
FinalSelector.lean:108:  | one (q : RMAF.Vertex)
FinalSelector.lean:109:  | first (cArc coreArc : RMAF.Vertex)
FinalSelector.lean:110:  | second (cArc coreArc : RMAF.Vertex)
FinalSelector.lean:111:  | third (cArc coreArc : RMAF.Vertex)
FinalSelector.lean:112:  deriving Repr, DecidableEq
```

## source-ForestColorWork-Charged.txt

```text
ForestColorWork.lean:9: structure Charged (α : Type) where
ForestColorWork.lean:10:   value : α
ForestColorWork.lean:11:   work : Nat
ForestColorWork.lean:12:   deriving Repr
```

## source-ForestColorWork-Colors_meterTagged.txt

```text
ForestColorWork.lean:195: structure Colors where
ForestColorWork.lean:196:   a : Local
ForestColorWork.lean:197:   b : Local
ForestColorWork.lean:198:   c : Local
ForestColorWork.lean:199:   deriving Repr

ForestColorWork.lean:204: def meterTagged (T : Tree) (A B : List Nat) (c : Colors) (x : Nat) : Charged Nat :=
ForestColorWork.lean:205:   let a := meterContains x A
ForestColorWork.lean:206:   if a.value then
ForestColorWork.lean:207:     let l := meterLocal T c.a x
ForestColorWork.lean:208:     ⟨3*l.value,a.work+l.work+4⟩
ForestColorWork.lean:209:   else
ForestColorWork.lean:210:     let b := meterContains x B
ForestColorWork.lean:211:     if b.value then
ForestColorWork.lean:212:       let l := meterLocal T c.b x
ForestColorWork.lean:213:       ⟨3*l.value+1,a.work+b.work+l.work+6⟩
ForestColorWork.lean:214:     else
ForestColorWork.lean:215:       let l := meterLocal T c.c x
ForestColorWork.lean:216:       ⟨3*l.value+2,a.work+b.work+l.work+6⟩
```

## source-ForestColorWork-Local_meterLocal.txt

```text
ForestColorWork.lean:146: inductive Local where
ForestColorWork.lean:147:   | keep
ForestColorWork.lean:148:   | single (v : RMAF.Vertex)
ForestColorWork.lean:149:   | joint (v w : RMAF.Vertex)
ForestColorWork.lean:150:   deriving Repr

ForestColorWork.lean:157: def meterLocal (T : Tree) (l : Local) (x : Nat) : Charged Nat :=
ForestColorWork.lean:158:   match l with
ForestColorWork.lean:159:   | .keep => ⟨0,1⟩
ForestColorWork.lean:160:   | .single v => meterColorLabel T v x
ForestColorWork.lean:161:   | .joint v w =>
ForestColorWork.lean:162:     let a := meterColorLabel T v x
ForestColorWork.lean:163:     let b := meterColorLabel T w x
ForestColorWork.lean:164:     ⟨4*a.value+b.value,a.work+b.work+3⟩
```

## source-ForestColorWork-meterColorLabel.txt

```text
ForestColorWork.lean:124: def meterColorLabel (T : Tree) (v : RMAF.Vertex) (x : Nat) : Charged Nat :=
ForestColorWork.lean:125:   let a := meterLeafList [x] T
ForestColorWork.lean:126:   let b := meterRegion v (a.value.headD [])
ForestColorWork.lean:127:   ⟨b.value,a.work+b.work+3⟩
```

## source-ForestColorWork-meterContains.txt

```text
ForestColorWork.lean:14: def meterContains (x : Nat) : List Nat → Charged Bool
ForestColorWork.lean:15:   | [] => ⟨false,1⟩
ForestColorWork.lean:16:   | y::ys => if x == y then ⟨true,4⟩ else
ForestColorWork.lean:17:       let r := meterContains x ys
ForestColorWork.lean:18:       ⟨r.value,4+r.work⟩
```

## source-ForestColorWork-meterLeafList.txt

```text
ForestColorWork.lean:35: def meterLeafList (D : List Nat) : Tree → Charged (List RMAF.Vertex)
ForestColorWork.lean:36:   | .leaf x =>
ForestColorWork.lean:37:     let m := meterContains x D
ForestColorWork.lean:38:     ⟨if m.value then [[]] else [],m.work+8⟩
ForestColorWork.lean:39:   | .node l r =>
ForestColorWork.lean:40:     let a := meterLeafList D l
ForestColorWork.lean:41:     let b := meterLeafList D r
ForestColorWork.lean:42:     ⟨prependSide false a.value ++ prependSide true b.value,
ForestColorWork.lean:43:       a.work+b.work+8*(a.value.length+b.value.length+1)⟩
```

## source-ForestColorWork-meterRegion.txt

```text
ForestColorWork.lean:92: def meterRegion : RMAF.Vertex → RMAF.Vertex → Charged Nat
ForestColorWork.lean:93:   | [], [] => ⟨3,2⟩
ForestColorWork.lean:94:   | [], false::_ => ⟨0,2⟩
ForestColorWork.lean:95:   | [], true::_ => ⟨1,2⟩
ForestColorWork.lean:96:   | _::_, [] => ⟨2,2⟩
ForestColorWork.lean:97:   | s::v,t::a => if s=t then
ForestColorWork.lean:98:       let r := meterRegion v a
ForestColorWork.lean:99:       ⟨r.value,4+r.work⟩ else ⟨2,4⟩
```

## source-ForestDefs-Overlap_jobs.txt

```text
ForestDefs.lean:12: structure Overlap where
ForestDefs.lean:13:   left : Nat
ForestDefs.lean:14:   right : Nat
ForestDefs.lean:15:   vertex : RMAF.Vertex
ForestDefs.lean:16:   deriving DecidableEq, Repr

ForestDefs.lean:33: def jobs (t : Tree) : List Tree → Option (List (Job (Tree × Tree) Forest))
ForestDefs.lean:34:   | [] => some []
ForestDefs.lean:35:   | s :: ss => (componentPair t s).bind fun p =>
ForestDefs.lean:36:     match DepthOne.pretest01 p.1 p.2 with
ForestDefs.lean:37:     | .refused => none
ForestDefs.lean:38:     | .rejected => (jobs t ss).map (.hard p :: ·)
ForestDefs.lean:39:     | .found c => (jobs t ss).map (.resolved p (DepthOne.cutCost c) (DepthOne.forest s c) :: ·)
```

## source-ForestDefs-componentPair.txt

```text
ForestDefs.lean:30: def componentPair (t s : Tree) : Option (Tree × Tree) :=
ForestDefs.lean:31:   (restrict (leaves s) t).map (fun u => (u,s))
```

## source-ForestDefs-disjointAttempt_overlap_raw_replace.txt

```text
ForestDefs.lean:18: def overlap (t : Tree) (ss : List Tree) : Option Overlap :=
ForestDefs.lean:19:   ((ss.zipIdx).flatMap fun a => (ss.zipIdx).filterMap fun b =>
ForestDefs.lean:20:     if a.2 < b.2 then
ForestDefs.lean:21:       ((minimalVertices (leaves a.1) t).find? fun v =>
ForestDefs.lean:22:         (minimalVertices (leaves b.1) t).contains v).map (Overlap.mk a.2 b.2)
ForestDefs.lean:23:     else none).head?

ForestDefs.lean:25: def replace (ss : List Tree) (i : Nat) (Q : Forest) : List Tree :=
ForestDefs.lean:26:   match ss[i]? with
ForestDefs.lean:27:   | none => ss
ForestDefs.lean:28:   | some s => ss.take i ++ sourceForest s Q ++ ss.drop (i+1)

ForestDefs.lean:41: def disjointAttempt (t : Tree) (ss : List Tree)
ForestDefs.lean:42:     (ordinary : Tree → Tree → Nat → Option Forest) (q : Nat) : Option (Receipt Forest) :=
ForestDefs.lean:43:   (jobs t ss).map (schedule (fun p b => (ordinary p.1 p.2 b).map (fun F => (F.length-1,F))) q)

ForestDefs.lean:45: def raw (t : Tree) (ss : List Tree) (i : Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
ForestDefs.lean:46:   match ss[i]? with
ForestDefs.lean:47:   | none => []
ForestDefs.lean:48:   | some s => (generate s (colorLabel t v) q).outputs
```

## source-ForestGeometryWork-meterAddressEq_meterVertexContains.txt

```text
ForestGeometryWork.lean:332: def meterAddressEq : RMAF.Vertex → RMAF.Vertex → Charged Bool
ForestGeometryWork.lean:333:   | [], [] => ⟨true,2⟩
ForestGeometryWork.lean:334:   | [], _::_ => ⟨false,2⟩
ForestGeometryWork.lean:335:   | _::_, [] => ⟨false,2⟩
ForestGeometryWork.lean:336:   | a::as,b::bs => if a == b then
ForestGeometryWork.lean:337:       let r := meterAddressEq as bs
ForestGeometryWork.lean:338:       ⟨r.value,4+r.work⟩ else ⟨false,4⟩

ForestGeometryWork.lean:361: def meterVertexContains (v : RMAF.Vertex) : List RMAF.Vertex → Charged Bool
ForestGeometryWork.lean:362:   | [] => ⟨false,1⟩
ForestGeometryWork.lean:363:   | w::ws =>
ForestGeometryWork.lean:364:     let h := meterAddressEq v w
ForestGeometryWork.lean:365:     if h.value then ⟨true,h.work+4⟩ else
ForestGeometryWork.lean:366:       let r := meterVertexContains v ws
ForestGeometryWork.lean:367:       ⟨r.value,h.work+r.work+4⟩
```

## source-ForestGeometryWork-meterAnyEq.txt

```text
ForestGeometryWork.lean:154: def meterAnyEq {α : Type} [BEq α] (a : α) : List α → Charged Bool
ForestGeometryWork.lean:155:   | [] => ⟨false,1⟩
ForestGeometryWork.lean:156:   | b::bs => if a == b then ⟨true,4⟩ else
ForestGeometryWork.lean:157:       let r := meterAnyEq a bs
ForestGeometryWork.lean:158:       ⟨r.value,4+r.work⟩
```

## source-ForestGeometryWork-meterCliqueSelection_meterRooted.txt

```text
ForestGeometryWork.lean:7: def meterRooted (D : List Nat) : Tree → Charged (List RMAF.Vertex)
ForestGeometryWork.lean:8:   | .leaf x =>
ForestGeometryWork.lean:9:     let m := meterContains x D
ForestGeometryWork.lean:10:     ⟨if m.value then [[]] else [],m.work+8⟩
ForestGeometryWork.lean:11:   | .node l r =>
ForestGeometryWork.lean:12:     let a := meterRooted D l
ForestGeometryWork.lean:13:     let b := meterRooted D r
ForestGeometryWork.lean:14:     ⟨if a.value.isEmpty && b.value.isEmpty then [] else
ForestGeometryWork.lean:15:       []::(prependSide false a.value ++ prependSide true b.value),
ForestGeometryWork.lean:16:       a.work+b.work+8*(a.value.length+b.value.length+2)⟩

ForestGeometryWork.lean:437: def meterCliqueSelection (T : Tree) (A B C : List Nat) : Charged (Option RMAF.Vertex) :=
ForestGeometryWork.lean:438:   let a := meterMinimal A T
ForestGeometryWork.lean:439:   let b := meterMinimal B T
ForestGeometryWork.lean:440:   let c := meterMinimal C T
ForestGeometryWork.lean:441:   let r := meterCommon a.value b.value c.value
ForestGeometryWork.lean:442:   ⟨r.value,a.work+b.work+c.work+r.work+4⟩
```

## source-ForestGeometryWork-meterCommon_meterJointColors.txt

```text
ForestGeometryWork.lean:244: def meterJointColors (D : List Nat) (T : Tree) (v w : RMAF.Vertex) : Charged (List (Nat×Nat)) :=
ForestGeometryWork.lean:245:   let a := meterLeafList D T
ForestGeometryWork.lean:246:   let b := meterJointMap v w a.value
ForestGeometryWork.lean:247:   let c := meterDups b.value
ForestGeometryWork.lean:248:   ⟨c.value,a.work+b.work+c.work+4⟩

ForestGeometryWork.lean:390: def meterCommon (A B C : List RMAF.Vertex) : Charged (Option RMAF.Vertex) :=
ForestGeometryWork.lean:391:   match A with
ForestGeometryWork.lean:392:   | [] => ⟨none,1⟩
ForestGeometryWork.lean:393:   | v::vs =>
ForestGeometryWork.lean:394:     let b := meterVertexContains v B
ForestGeometryWork.lean:395:     let c := meterVertexContains v C
ForestGeometryWork.lean:396:     if b.value && c.value then ⟨some v,b.work+c.work+6⟩ else
ForestGeometryWork.lean:397:       let r := meterCommon vs B C
ForestGeometryWork.lean:398:       ⟨r.value,b.work+c.work+r.work+6⟩
```

## source-ForestGeometryWork-meterDupsLoop.txt

```text
ForestGeometryWork.lean:174: def meterDupsLoop {α : Type} [BEq α] : List α → List α → Charged (List α)
ForestGeometryWork.lean:175:   | [], acc => ⟨acc.reverse,4*(acc.length+1)⟩
ForestGeometryWork.lean:176:   | a::as, acc =>
ForestGeometryWork.lean:177:     let h := meterAnyEq a acc
ForestGeometryWork.lean:178:     let r := if h.value then meterDupsLoop as acc else meterDupsLoop as (a::acc)
ForestGeometryWork.lean:179:     ⟨r.value,h.work+r.work+4⟩
```

## source-ForestGeometryWork-meterDups_meterJointMap.txt

```text
ForestGeometryWork.lean:207: def meterDups {α : Type} [BEq α] (L : List α) : Charged (List α) := meterDupsLoop L []

ForestGeometryWork.lean:217: def meterJointMap (v w : RMAF.Vertex) : List RMAF.Vertex → Charged (List (Nat×Nat))
ForestGeometryWork.lean:218:   | [] => ⟨[],1⟩
ForestGeometryWork.lean:219:   | a::as =>
ForestGeometryWork.lean:220:     let p := meterRegion v a
ForestGeometryWork.lean:221:     let q := meterRegion w a
ForestGeometryWork.lean:222:     let r := meterJointMap v w as
ForestGeometryWork.lean:223:     ⟨(p.value,q.value)::r.value,p.work+q.work+r.work+6⟩
```

## source-ForestGeometryWork-meterMinimal.txt

```text
ForestGeometryWork.lean:63: def meterMinimal (D : List Nat) : Tree → Charged (List RMAF.Vertex)
ForestGeometryWork.lean:64:   | .leaf x =>
ForestGeometryWork.lean:65:     let m := meterContains x D
ForestGeometryWork.lean:66:     ⟨if m.value then [[]] else [],m.work+8⟩
ForestGeometryWork.lean:67:   | .node l r =>
ForestGeometryWork.lean:68:     let a := meterRooted D l
ForestGeometryWork.lean:69:     let b := meterRooted D r
ForestGeometryWork.lean:70:     if a.value.isEmpty then
ForestGeometryWork.lean:71:       let m := meterMinimal D r
ForestGeometryWork.lean:72:       ⟨prependSide true m.value,a.work+b.work+m.work+8*(m.value.length+2)⟩
ForestGeometryWork.lean:73:     else if b.value.isEmpty then
ForestGeometryWork.lean:74:       let m := meterMinimal D l
ForestGeometryWork.lean:75:       ⟨prependSide false m.value,a.work+b.work+m.work+8*(m.value.length+2)⟩
ForestGeometryWork.lean:76:     else
ForestGeometryWork.lean:77:       ⟨[]::(prependSide false a.value++prependSide true b.value),
ForestGeometryWork.lean:78:         a.work+b.work+8*(a.value.length+b.value.length+2)⟩
```

## source-ForestMerge-merged.txt

```text
ForestMerge.lean:5: def merged (K L : List Nat) (FX FY : List (List Nat)) := (K++L)::(FX++FY)
```

## source-ForestPretest01-Result.txt

```text
ForestPretest01.lean:22: inductive Result where
ForestPretest01.lean:23:   | refused
ForestPretest01.lean:24:   | rejected
ForestPretest01.lean:25:   | found (F : Forest)
ForestPretest01.lean:26:   deriving DecidableEq, Repr
```

## source-ForestPretestSource-forestPretestMeter.txt

```text
ForestPretestSource.lean:35: def forestPretestMeter (T : Option Tree) (ss : List Tree) : Charged ForestPretest01.Result:=
ForestPretestSource.lean:36:  let p:=meterProper T ss
ForestPretestSource.lean:37:  if p.value then
ForestPretestSource.lean:38:   let c:=pretestCandidatesMeter ss
ForestPretestSource.lean:39:   let b:=sourceBestMeter (additionalCostMeter ss) (meterAgrees T ss) c.value
ForestPretestSource.lean:40:   ⟨match b.value with | none=>.rejected | some F=>.found F,p.work+c.work+b.work+16⟩
ForestPretestSource.lean:41:  else ⟨.refused,p.work+8⟩
```

## source-ForestPretestSource-oneCutsForestMeter_unchangedForestMeter.txt

```text
ForestPretestSource.lean:6: def unchangedForestMeter (ss : List Tree) : Charged (List (List Nat)):=meterMap meterLeaves ss

ForestPretestSource.lean:12: def oneCutsForestMeter : List Tree→Charged (List (List (List Nat)))
ForestPretestSource.lean:13:  | []=>⟨[],2⟩
ForestPretestSource.lean:14:  | s::ss=>
ForestPretestSource.lean:15:    let edges:=meterEdges s
ForestPretestSource.lean:16:    let head:=meterMap (fun p=>let f:=meterForest s (some p);let u:=unchangedForestMeter ss
ForestPretestSource.lean:17:       ⟨f.value++u.value,f.work+u.work+2*f.value.length+8⟩) edges.value
ForestPretestSource.lean:18:    let tail:=oneCutsForestMeter ss
ForestPretestSource.lean:19:    let lift:=meterMap (fun F=>let l:=meterLeaves s;⟨l.value::F,l.work+8⟩) tail.value
ForestPretestSource.lean:20:    ⟨head.value++lift.value,edges.work+head.work+tail.work+lift.work+2*head.value.length+12⟩
```

## source-ForestPretestSource-pretestCandidatesMeter.txt

```text
ForestPretestSource.lean:28: def pretestCandidatesMeter (ss : List Tree) : Charged (List (List (List Nat))):=
ForestPretestSource.lean:29:  let u:=unchangedForestMeter ss;let c:=oneCutsForestMeter ss
ForestPretestSource.lean:30:  ⟨u.value::c.value,u.work+c.work+4⟩
```

## source-ForestProgram-accepted.txt

```text
ForestProgram.lean:6: def accepted (T : Option Tree) (ss : List Tree) (q : Nat) (F : Forest) : Bool :=
ForestProgram.lean:7:   agrees T ss F && decide (additionalCost ss F ≤ q)
```

## source-FullStateJobs-Problem.txt

```text
FullStateJobs.lean:8: structure Problem where
FullStateJobs.lean:9:  key : List Nat
FullStateJobs.lean:10:  target : Option Tree
FullStateJobs.lean:11:  sources : List Tree
FullStateJobs.lean:12:  deriving DecidableEq, Repr
```

## source-GeneralAgreementWork-agreementMeter.txt

```text
GeneralAgreementWork.lean:10: def agreementMeter (T S : Tree) (F : List (List Nat)) : Charged Bool :=
GeneralAgreementWork.lean:11:  let t:=meterLeaves T;let s:=meterLeaves S
GeneralAgreementWork.lean:12:  let pt:=meterPartition t.value F;let ps:=meterPartition s.value F
GeneralAgreementWork.lean:13:  let r:=meterAll (meterRestrictionAgrees T S) F
GeneralAgreementWork.lean:14:  let a:=meterPairwise T F;let b:=meterPairwise S F
GeneralAgreementWork.lean:15:  ⟨pt.value&&ps.value&&r.value&&a.value&&b.value,
GeneralAgreementWork.lean:16:   t.work+s.work+pt.work+ps.work+r.work+a.work+b.work+8⟩
```

## source-GeneralAgreementWork-measuredAgreement.txt

```text
GeneralAgreementWork.lean:52: def measuredAgreement (T S : Tree) (F : List (List Nat)) : Rule5LocalWork.Measured Bool :=
GeneralAgreementWork.lean:53:  let c:=agreementMeter T S F;⟨c.value,c.work⟩
```

## source-Geometry-region.txt

```text
Geometry.lean:35: def region : Vertex → Vertex → Nat
Geometry.lean:36:   | [], [] => 3
Geometry.lean:37:   | [], false :: _ => 0
Geometry.lean:38:   | [], true :: _ => 1
Geometry.lean:39:   | _ :: _, [] => 2
Geometry.lean:40:   | s :: v, t :: a => if s = t then region v a else 2
```

## source-GoodPairSource-goodPairLocalSource.txt

```text
GoodPairSource.lean:10: def goodPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
GoodPairSource.lean:11:  (A B C : List Nat) (q : Nat) : SourceExecution:=
GoodPairSource.lean:12:  if 2≤q then
GoodPairSource.lean:13:   let ss:=sourceForestMeter S [A,B,C]
GoodPairSource.lean:14:   let u1:=appendLabelsMeter A B;let t:=localTargetMeter (some T) u1.value
GoodPairSource.lean:15:   let u2:=appendLabelsMeter A B;let ds:=ownedMeter ss.value u2.value
GoodPairSource.lean:16:   let dp:=AllGoodDP.LocalWork.meterRun t.value ds.value
GoodPairSource.lean:17:   let frontWork:=ss.work+u1.work+t.work+u2.work+ds.work+dp.work+12
GoodPairSource.lean:18:   match dp.value with
GoodPairSource.lean:19:   | none=>⟨⟨none,[]⟩,frontWork+4⟩
GoodPairSource.lean:20:   | some H=>
GoodPairSource.lean:21:    let u3:=appendLabelsMeter A B;let scoreSources:=ownedMeter ss.value u3.value
GoodPairSource.lean:22:    let score:=additionalCostMeter scoreSources.value H
GoodPairSource.lean:23:    let firstWork:=frontWork+u3.work+scoreSources.work+score.work+8
GoodPairSource.lean:24:    if score.value≤q-2 then
GoodPairSource.lean:25:     let target:=localTargetMeter (some T) C;let sources:=ownedMeter ss.value C
GoodPairSource.lean:26:     let r:=q-2-score.value
GoodPairSource.lean:27:     let answer:=GenericForest.solve actual target.value sources.value r
GoodPairSource.lean:28:     let checked:=checkedMeter T S q (answer.map (fun K=>H++K))
GoodPairSource.lean:29:     ⟨⟨checked.value,[⟨target.value,sources.value,r⟩]⟩,
GoodPairSource.lean:30:      firstWork+target.work+sources.work+2*H.length+checked.work+16⟩
GoodPairSource.lean:31:    else ⟨⟨none,[]⟩,firstWork+4⟩
GoodPairSource.lean:32:  else ⟨⟨none,[]⟩,6⟩
```

## source-GoodPairSource-goodPairSource.txt

```text
GoodPairSource.lean:51: def goodPairSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
GoodPairSource.lean:52:  (T S : Tree) (A B C : List Nat) (q : Nat) : SourceExecution:=
GoodPairSource.lean:53:  let r:=goodPairLocalSource actual T S A B C q
GoodPairSource.lean:54:  ⟨r.value,r.work+callsForestDebit actual W r.value.calls⟩
```

## source-GroupPartition-contained.txt

```text
GroupPartition.lean:5: def contained (B U : List Nat) : Bool := B.all (U.contains ·)
```

## source-GroupPartition-family.txt

```text
GroupPartition.lean:6: def family (U : List Nat) (F : List (List Nat)) := F.filter (contained · U)
```

## source-GroupState-additionalCost.txt

```text
GroupState.lean:31: def additionalCost (ss : List Tree) (F : List (List Nat)) := F.length - ss.length
```

## source-GroupState-agrees_proper.txt

```text
GroupState.lean:19: def proper (T : Option Tree) (ss : List Tree) : Bool :=
GroupState.lean:20:   decide (labels T).Nodup && partitionCheck (labels T) (ss.map leaves)

GroupState.lean:26: def agrees (T : Option Tree) (ss : List Tree) (F : List (List Nat)) : Bool :=
GroupState.lean:27:   proper T ss && partitionCheck (labels T) F &&
GroupState.lean:28:   F.all (fun B => ss.any (fun s => contained B (leaves s))) &&
GroupState.lean:29:   targetEmbeddings T F && ss.all (sourceCheck T F)
```

## source-GroupState-labels_sourceCheck_targetEmbeddings.txt

```text
GroupState.lean:7: def labels : Option Tree → List Nat
GroupState.lean:8:   | none => []
GroupState.lean:9:   | some t => leaves t

GroupState.lean:11: def targetEmbeddings : Option Tree → List (List Nat) → Bool
GroupState.lean:12:   | none, F => F.isEmpty
GroupState.lean:13:   | some t, F => pairwiseEmbeddings t F

GroupState.lean:22: def sourceCheck (T : Option Tree) (F : List (List Nat)) (s : Tree) : Bool :=
GroupState.lean:23:   let G := family (leaves s) F
GroupState.lean:24:   partitionCheck (leaves s) G && G.all (targetAgrees T s) && pairwiseEmbeddings s G
```

## source-GroupState-targetAgrees.txt

```text
GroupState.lean:15: def targetAgrees : Option Tree → Tree → List Nat → Bool
GroupState.lean:16:   | none, _, _ => false
GroupState.lean:17:   | some t, s, B => restrictionAgrees t s B
```

## source-GroupedExecutionSource-GroupEvaluationSource_groupOutputAnswerMeter.txt

```text
GroupedExecutionSource.lean:8: def groupOutputAnswerMeter (r : BothBadGrouped.OutputResult) : Charged (Option (List (List Nat))):=
GroupedExecutionSource.lean:9:  match r with
GroupedExecutionSource.lean:10:  | .scheduled s=>let f:=optionFlattenMeter s.value.answers;⟨f.value,f.work+4⟩
GroupedExecutionSource.lean:11:  | _=>⟨none,4⟩

GroupedExecutionSource.lean:16: structure GroupEvaluationSource where
GroupedExecutionSource.lean:17:  value : BothBadGrouped.Evaluation
GroupedExecutionSource.lean:18:  work : Nat
```

## source-GroupedExecutionSource-GroupPairSourceExecution_bothBadOutputsMeter_forestLengthMeter_groupEvaluateLocalSource_groupedAcceptedMeter.txt

```text
GroupedExecutionSource.lean:20: def groupEvaluateLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
GroupedExecutionSource.lean:21:  (A B C : List Nat) (q : Nat) : List CoreProgram.Output→GroupEvaluationSource
GroupedExecutionSource.lean:22:  | []=>⟨⟨[],[]⟩,2⟩
GroupedExecutionSource.lean:23:  | o::os=>let r:=groupRunOutputLocalSource actual T S A B C q o
GroupedExecutionSource.lean:24:    let a:=groupOutputAnswerMeter r.value
GroupedExecutionSource.lean:25:    let tail:=groupEvaluateLocalSource actual T S A B C q os
GroupedExecutionSource.lean:26:    ⟨⟨a.value.toList++tail.value.candidates,r.value.trace++tail.value.queries⟩,
GroupedExecutionSource.lean:27:     r.work+a.work+tail.work+2*r.value.trace.length+20⟩

GroupedExecutionSource.lean:36: def bothBadOutputsMeter (S : Tree) (A B D : List Nat) (q : Nat) : Charged (List CoreProgram.Output):=
GroupedExecutionSource.lean:37:  appendOutputsMeter (generatedOutputsMeter S (cheapColorMeter A B D) q)
GroupedExecutionSource.lean:38:   (generatedOutputsMeter S (cheapColorMeter B A D) q)

GroupedExecutionSource.lean:46: def groupedAcceptedMeter (T S : Tree) (q : Nat) (F : List (List Nat)) : Charged Bool:=
GroupedExecutionSource.lean:47:  let a:=agreementMeter T S F
GroupedExecutionSource.lean:48:  ⟨a.value&&decide (F.length-1≤q),a.work+F.length+8⟩

GroupedExecutionSource.lean:53: def forestLengthMeter (F : List (List Nat)) : Charged Nat:=⟨F.length,F.length+4⟩

GroupedExecutionSource.lean:56: structure GroupPairSourceExecution where
GroupedExecutionSource.lean:57:  value : BothBadGrouped.PairExecution
GroupedExecutionSource.lean:58:  work : Nat
```

## source-GroupedExecutionSource-groupCalls_groupPairLocalSource.txt

```text
GroupedExecutionSource.lean:60: def groupPairLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
GroupedExecutionSource.lean:61:  (A B C : List Nat) (edge : RMAF.Vertex×RMAF.Vertex) (q : Nat) : GroupPairSourceExecution:=
GroupedExecutionSource.lean:62:  let d:=pairDescendantsMeter T edge.2
GroupedExecutionSource.lean:63:  let o:=bothBadOutputsMeter S A B d.value q
GroupedExecutionSource.lean:64:  let e:=groupEvaluateLocalSource actual T S A B C q o.value
GroupedExecutionSource.lean:65:  let best:=sourceBestMeter forestLengthMeter (groupedAcceptedMeter T S q) e.value.candidates
GroupedExecutionSource.lean:66:  ⟨⟨best.value,e.value.queries⟩,d.work+o.work+e.work+best.work+20⟩

GroupedExecutionSource.lean:75: def groupCalls (xs : List (Problem×Nat)) : List Call:=xs.map (fun x=>⟨x.1.target,x.1.sources,x.2⟩)
```

## source-GroupedJobsSource-groupCallbackMeter_groupJobsForMeter.txt

```text
GroupedJobsSource.lean:46: def groupCallbackMeter (actual : GenericForest.FrontierWork.Ordinary) (p : Problem) (b : Nat) :
GroupedJobsSource.lean:47:  Charged (Option (Nat×List (List Nat))):=
GroupedJobsSource.lean:48:  let answer:=GenericForest.solve actual p.target p.sources b
GroupedJobsSource.lean:49:  match answer with
GroupedJobsSource.lean:50:  | none=>⟨none,4⟩
GroupedJobsSource.lean:51:  | some F=>let c:=additionalCostMeter p.sources F
GroupedJobsSource.lean:52:            ⟨some (c.value,F),c.work+12⟩

GroupedJobsSource.lean:58: def groupJobsForMeter (T S : Tree) (A B C : List Nat) (o : CoreProgram.Output) :
GroupedJobsSource.lean:59:  Charged (Option (List (Job Problem (List (List Nat))))):=
GroupedJobsSource.lean:60:  let ss:=Universal233.Rule5SelectedLocalWork.sourceForestMeter S o.partition
GroupedJobsSource.lean:61:  let ab:=appendLabelsMeter A B
GroupedJobsSource.lean:62:  let groups:=groupProblemsMeter (some T) ss.value [ab.value,C]
GroupedJobsSource.lean:63:  let jobs:=groupPrepareMeter groups.value
GroupedJobsSource.lean:64:  ⟨jobs.value,ss.work+ab.work+groups.work+jobs.work+16⟩
```

## source-GroupedJobsSource-groupPrepareMeter_groupProblemsMeter.txt

```text
GroupedJobsSource.lean:16: def groupProblemsMeter (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) : Charged (List Problem):=
GroupedJobsSource.lean:17:  meterMap (groupProblemMeter T ss) Q

GroupedJobsSource.lean:34: def groupPrepareMeter : List Problem→Charged (Option (List (Job Problem (List (List Nat)))))
GroupedJobsSource.lean:35:  | []=>⟨some [],2⟩
GroupedJobsSource.lean:36:  | p::ps=>let a:=groupPrepareOneMeter p;let r:=groupPrepareMeter ps
GroupedJobsSource.lean:37:            ⟨a.value.bind (fun j=>r.value.map (j::·)),a.work+r.work+8⟩
```

## source-GroupedJobsSource-groupPrepareOneMeter_groupProblemMeter.txt

```text
GroupedJobsSource.lean:9: def groupProblemMeter (T : Option Tree) (ss : List Tree) (U : List Nat) : Charged Problem:=
GroupedJobsSource.lean:10:  let t:=localTargetMeter T U;let s:=ownedMeter ss U
GroupedJobsSource.lean:11:  ⟨⟨U,t.value,s.value⟩,t.work+s.work+12⟩

GroupedJobsSource.lean:22: def groupPrepareOneMeter (p : Problem) : Charged (Option (Job Problem (List (List Nat)))):=
GroupedJobsSource.lean:23:  let pre:=forestPretestMeter p.target p.sources
GroupedJobsSource.lean:24:  match pre.value with
GroupedJobsSource.lean:25:  | .refused=>⟨none,pre.work+8⟩
GroupedJobsSource.lean:26:  | .rejected=>⟨some (.hard p),pre.work+12⟩
GroupedJobsSource.lean:27:  | .found F=>let c:=additionalCostMeter p.sources F
GroupedJobsSource.lean:28:              ⟨some (.resolved p c.value F),pre.work+c.work+16⟩
```

## source-GroupedJobsSource-groupRunOutputLocalSource.txt

```text
GroupedJobsSource.lean:71: def groupRunOutputLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
GroupedJobsSource.lean:72:  (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) : Charged BothBadGrouped.OutputResult:=
GroupedJobsSource.lean:73:  if o.sourceCuts.length≤q then
GroupedJobsSource.lean:74:   let j:=groupJobsForMeter T S A B C o
GroupedJobsSource.lean:75:   match j.value with
GroupedJobsSource.lean:76:   | none=>⟨.refused,2*o.sourceCuts.length+j.work+12⟩
GroupedJobsSource.lean:77:   | some js=>let r:=literalScheduleSource (groupCallbackMeter actual) (q-o.sourceCuts.length) js
GroupedJobsSource.lean:78:              ⟨.scheduled r.value,2*o.sourceCuts.length+j.work+r.localWork+r.callbackWork+20⟩
GroupedJobsSource.lean:79:  else ⟨.unaffordable,o.sourceCuts.length+8⟩
```

## source-GuardCost-meterGuard.txt

```text
GuardCost.lean:13: def meterGuard (T : Option Tree) (ss : List Tree) : Charged Bool :=
GuardCost.lean:14:  let p := GenericForest.CheckCorrespondence.meterProper T ss
GuardCost.lean:15:  let s := GenericForest.CheckCorrespondence.meterAll (meterSourceGuard T) ss
GuardCost.lean:16:  ⟨p.value&&s.value,p.work+s.work+4⟩
```

## source-GuardCost-meterRun.txt

```text
GuardCost.lean:42: def meterRun (T : Option Tree) (ss : List Tree) : Charged (Option (List (List Nat))) :=
GuardCost.lean:43:  let g := meterGuard T ss
GuardCost.lean:44:  if g.value then
GuardCost.lean:45:   let c := meterCandidate T ss
GuardCost.lean:46:   ⟨some c.value,g.work+c.work+8⟩
GuardCost.lean:47:  else ⟨none,g.work+4⟩
```

## source-GuardCost-meterSourceGuard.txt

```text
GuardCost.lean:6: def meterSourceGuard (T : Option Tree) (s : Tree) : Charged Bool :=
GuardCost.lean:7:  let l := GenericForest.CheckCorrespondence.meterLeaves s
GuardCost.lean:8:  let g := GenericForest.CheckCorrespondence.meterTargetAgrees T s l.value
GuardCost.lean:9:  ⟨g.value,l.work+g.work+4⟩
```

## source-Hard2FullOutputSource-SourceExecution_chooseMeter.txt

```text
Hard2FullOutputSource.lean:15: def chooseMeter : Option (List (List Nat))→Option (List (List Nat))→Charged (Option (List (List Nat)))
Hard2FullOutputSource.lean:16:  | none,b=>⟨b,2⟩
Hard2FullOutputSource.lean:17:  | a,none=>⟨a,2⟩
Hard2FullOutputSource.lean:18:  | some F,some G=>⟨if F.length≤G.length then some F else some G,F.length+G.length+4⟩

Hard2FullOutputSource.lean:22: structure SourceExecution where
Hard2FullOutputSource.lean:23:  value : Execution
Hard2FullOutputSource.lean:24:  work : Nat
```

## source-Hard2FullOutputSource-checkedMeter.txt

```text
Hard2FullOutputSource.lean:8: def checkedMeter (T S : Tree) (q : Nat) : Option (List (List Nat))→Charged (Option (List (List Nat)))
Hard2FullOutputSource.lean:9:  | none=>⟨none,2⟩
Hard2FullOutputSource.lean:10:  | some F=>let a:=agreementMeter T S F
Hard2FullOutputSource.lean:11:            ⟨if a.value && decide (F.length-1≤q) then some F else none,a.work+F.length+6⟩
```

## source-Hard2FullOutputSource-fullOutputsSource.txt

```text
Hard2FullOutputSource.lean:29: def fullOutputsSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
Hard2FullOutputSource.lean:30:  (T S : Tree) (q : Nat) : List CoreProgram.Output→SourceExecution
Hard2FullOutputSource.lean:31:  | []=>⟨⟨none,[]⟩,2⟩
Hard2FullOutputSource.lean:32:  | o::os=>
Hard2FullOutputSource.lean:33:   let r:=fullOutputsSource actual W T S q os
Hard2FullOutputSource.lean:34:   if o.sourceCuts.length≤q then
Hard2FullOutputSource.lean:35:    let ss:=sourceForestMeter S o.partition
Hard2FullOutputSource.lean:36:    let answer:=GenericForest.solve actual (some T) ss.value (q-o.sourceCuts.length)
Hard2FullOutputSource.lean:37:    let c:=checkedMeter T S q answer;let b:=chooseMeter c.value r.value.answer
Hard2FullOutputSource.lean:38:    ⟨⟨b.value,⟨some T,ss.value,q-o.sourceCuts.length⟩::r.value.calls⟩,
Hard2FullOutputSource.lean:39:     2*o.sourceCuts.length+ss.work+forestWork actual W (some T) ss.value (q-o.sourceCuts.length)+
Hard2FullOutputSource.lean:40:     c.work+b.work+r.work+14⟩
Hard2FullOutputSource.lean:41:   else ⟨r.value,2*o.sourceCuts.length+r.work+6⟩
```

## source-Hard2GeneratorSource-appendOutputsMeter_generatedOutputsMeter_wholeOutputsMeter.txt

```text
Hard2GeneratorSource.lean:9: def generatedOutputsMeter (S : Tree) (color : Nat→Charged Nat) (q : Nat) : Charged (List Output) :=
Hard2GeneratorSource.lean:10:  let r:=RecoveryLocalWork.meterGenerate S color q
Hard2GeneratorSource.lean:11:  ⟨r.value.outputs,r.work+4⟩

Hard2GeneratorSource.lean:36: def appendOutputsMeter (a b : Charged (List Output)) : Charged (List Output) :=
Hard2GeneratorSource.lean:37:  ⟨a.value++b.value,a.work+b.work+2*a.value.length+4⟩

Hard2GeneratorSource.lean:41: def wholeOutputsMeter (S T : Tree) (A B : List Nat) (c : Colors) (q : Nat) : Charged (List Output) :=
Hard2GeneratorSource.lean:42:  generatedOutputsMeter S (meterTagged T A B c) q
```

## source-Hard2GraphSource-hard2ChainMeter_hard2IsolatedMeter_hard2OverlapMeter_hard2RootMeter.txt

```text
Hard2GraphSource.lean:9: def hard2RootMeter (S : Tree) (p r : RMAF.Vertex) : Charged (List Nat) :=
Hard2GraphSource.lean:10:  let l:=meterLeaves S
Hard2GraphSource.lean:11:  let c:=meterFilter (fun x=>let a:=subtreeLabelsMeter S p;let b:=subtreeLabelsMeter S r
Hard2GraphSource.lean:12:   let ca:=meterContains x a.value;let cb:=meterContains x b.value
Hard2GraphSource.lean:13:   ⟨!ca.value&&!cb.value,a.work+b.work+ca.work+cb.work+4⟩) l.value
Hard2GraphSource.lean:14:  ⟨c.value,l.work+c.work+2⟩

Hard2GraphSource.lean:26: def hard2OverlapMeter (T : Tree) (A B : List Nat) : Charged (Option RMAF.Vertex) :=
Hard2GraphSource.lean:27:  let a:=meterMinimal A T;let b:=meterMinimal B T;let b2:=meterMinimal B T
Hard2GraphSource.lean:28:  let c:=meterCommon a.value b.value b2.value
Hard2GraphSource.lean:29:  ⟨c.value,a.work+b.work+b2.work+c.work+4⟩

Hard2GraphSource.lean:33: def hard2ChainMeter (T : Tree) (A B C : List Nat) (o : Order) (v w : RMAF.Vertex) : Charged Result :=
Hard2GraphSource.lean:34:  let j:=meterJointColors (second o A B C) T v w
Hard2GraphSource.lean:35:  ⟨if j.value.length=2 then .diagonal o v w else .four o v w,j.work+j.value.length+8⟩

Hard2GraphSource.lean:39: def hard2IsolatedMeter (T : Tree) (A B C : List Nat) (o : Order) : Charged (Option Result) :=
Hard2GraphSource.lean:40:  let p:=pairChooseMeter T (first o A B C) (second o A B C)
Hard2GraphSource.lean:41:  ⟨p.value.map (Result.pair o),p.work+6⟩
```

## source-Hard2GraphSource-hard2ParentsMeter_hard2SelectMeter.txt

```text
Hard2GraphSource.lean:19: def hard2ParentsMeter (S : Tree) (p r : RMAF.Vertex) : Charged (List Nat×List Nat×List Nat) :=
Hard2GraphSource.lean:20:  let a:=subtreeLabelsMeter S p;let b:=subtreeLabelsMeter S r;let c:=hard2RootMeter S p r
Hard2GraphSource.lean:21:  ⟨(a.value,b.value,c.value),a.work+b.work+c.work+4⟩

Hard2GraphSource.lean:45: def hard2SelectMeter (T : Tree) (A B C : List Nat) : Charged (Option Result) :=
Hard2GraphSource.lean:46:  let ab:=hard2OverlapMeter T A B;let bc:=hard2OverlapMeter T B C;let ac:=hard2OverlapMeter T A C
Hard2GraphSource.lean:47:  let frontWork:=ab.work+bc.work+ac.work+8
Hard2GraphSource.lean:48:  match ab.value,bc.value,ac.value with
Hard2GraphSource.lean:49:  | none,none,none=>⟨some .disjoint,frontWork⟩
Hard2GraphSource.lean:50:  | some v,some w,none=>let r:=hard2ChainMeter T A B C .abc v w;⟨some r.value,frontWork+r.work⟩
Hard2GraphSource.lean:51:  | some v,none,some w=>let r:=hard2ChainMeter T A B C .bac v w;⟨some r.value,frontWork+r.work⟩
Hard2GraphSource.lean:52:  | none,some w,some v=>let r:=hard2ChainMeter T A B C .acb v w;⟨some r.value,frontWork+r.work⟩
Hard2GraphSource.lean:53:  | some _,none,none=>let r:=hard2IsolatedMeter T A B C .abc;⟨r.value,frontWork+r.work⟩
Hard2GraphSource.lean:54:  | none,none,some _=>let r:=hard2IsolatedMeter T A B C .acb;⟨r.value,frontWork+r.work⟩
Hard2GraphSource.lean:55:  | none,some _,none=>let r:=hard2IsolatedMeter T A B C .bca;⟨r.value,frontWork+r.work⟩
Hard2GraphSource.lean:56:  | some _,some _,some _=>let r:=meterCliqueSelection T A B C;⟨r.value.map Result.clique,frontWork+r.work+2⟩
```

## source-Hard2GraphSource-runHard2Meter.txt

```text
Hard2GraphSource.lean:62: def runHard2Meter (T S : Tree) (c : CherryBranching.Candidate) : Charged (Option Result) :=
Hard2GraphSource.lean:63:  match c.originalCuts with
Hard2GraphSource.lean:64:  | [p,r]=>let parents:=hard2ParentsMeter S p r
Hard2GraphSource.lean:65:           let s:=hard2SelectMeter T parents.value.1 parents.value.2.1 parents.value.2.2
Hard2GraphSource.lean:66:           ⟨s.value,parents.work+s.work+8⟩
Hard2GraphSource.lean:67:  | _=>⟨none,8⟩
```

## source-Hard2GroupingSource-additionalCostMeter_appendLabelsMeter_localTargetMeter_ownedMeter.txt

```text
Hard2GroupingSource.lean:11: def appendLabelsMeter (A B : List Nat) : Charged (List Nat):=⟨A++B,2*A.length+4⟩

Hard2GroupingSource.lean:14: def localTargetMeter (T : Option Tree) (U : List Nat) : Charged (Option Tree) :=
Hard2GroupingSource.lean:15:  match T with
Hard2GroupingSource.lean:16:  | none=>⟨none,2⟩
Hard2GroupingSource.lean:17:  | some t=>let r:=meterRestrict U t;⟨r.value,r.work+4⟩

Hard2GroupingSource.lean:22: def ownedMeter (ss : List Tree) (U : List Nat) : Charged (List Tree) :=
Hard2GroupingSource.lean:23:  meterFilter (fun s=>let l:=meterLeaves s;let c:=meterContained l.value U
Hard2GroupingSource.lean:24:   ⟨c.value,l.work+c.work+4⟩) ss

Hard2GroupingSource.lean:28: def additionalCostMeter (ss : List Tree) (F : List (List Nat)) : Charged Nat:=
Hard2GroupingSource.lean:29:  ⟨F.length-ss.length,F.length+ss.length+4⟩
```

## source-Hard2GroupingSource-callsForestDebit.txt

```text
Hard2GroupingSource.lean:34: def callsForestDebit (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork) (calls : List Call) : Nat:=
Hard2GroupingSource.lean:35:  (calls.map fun call=>forestWork actual W call.target call.sources call.budget).sum
```

## source-Hard2OutputGenerationSource-actualOutputsMeter.txt

```text
Hard2OutputGenerationSource.lean:71: def actualOutputsMeter (S T : Tree) (c : CherryBranching.Candidate) (q : Nat) (out : Result) : Charged (List Output) :=
Hard2OutputGenerationSource.lean:72:  match c.originalCuts with
Hard2OutputGenerationSource.lean:73:  | [p,r]=>let parents:=hard2ParentsMeter S p r
Hard2OutputGenerationSource.lean:74:           let os:=caseOutputsMeter S T parents.value.1 parents.value.2.1 parents.value.2.2 q out
Hard2OutputGenerationSource.lean:75:           ⟨os.value,parents.work+os.work+8⟩
Hard2OutputGenerationSource.lean:76:  | _=>⟨[],8⟩
```

## source-Hard2OutputGenerationSource-caseOutputsMeter.txt

```text
Hard2OutputGenerationSource.lean:58: def caseOutputsMeter (S T : Tree) (A B C : List Nat) (q : Nat) : Result→Charged (List Output)
Hard2OutputGenerationSource.lean:59:  | .disjoint=>⟨[],2⟩
Hard2OutputGenerationSource.lean:60:  | .clique v=>kindOutputsMeter (.clique v) S T A B q
Hard2OutputGenerationSource.lean:61:  | .four o v w=>kindOutputsMeter (.four v w) S T (first o A B C) (second o A B C) q
Hard2OutputGenerationSource.lean:62:  | .diagonal o v w=>kindOutputsMeter (.diagonal v w) S T (first o A B C) (second o A B C) q
Hard2OutputGenerationSource.lean:63:  | .pair o (.vertex v)=>kindOutputsMeter (.vertex v) S T (first o A B C) (second o A B C) q
Hard2OutputGenerationSource.lean:64:  | .pair o (.edge e)=>edgeOutputsMeter S T (first o A B C) (second o A B C) e q
```

## source-Hard2OutputGenerationSource-edgeOutputsMeter_kindOutputsMeter.txt

```text
Hard2OutputGenerationSource.lean:19: def kindOutputsMeter (kind : Kind) (S T : Tree) (A B : List Nat) (q : Nat) : Charged (List Output) :=
Hard2OutputGenerationSource.lean:20:  match kind with
Hard2OutputGenerationSource.lean:21:  | .clique v=>
Hard2OutputGenerationSource.lean:22:   appendOutputsMeter
Hard2OutputGenerationSource.lean:23:    (appendOutputsMeter (wholeOutputsMeter S T A B ⟨.keep,.single v,.single v⟩ q)
Hard2OutputGenerationSource.lean:24:     (wholeOutputsMeter S T A B ⟨.single v,.keep,.single v⟩ q))
Hard2OutputGenerationSource.lean:25:    (wholeOutputsMeter S T A B ⟨.single v,.single v,.keep⟩ q)
Hard2OutputGenerationSource.lean:26:  | .four v w=>
Hard2OutputGenerationSource.lean:27:   appendOutputsMeter
Hard2OutputGenerationSource.lean:28:    (appendOutputsMeter
Hard2OutputGenerationSource.lean:29:     (appendOutputsMeter (wholeOutputsMeter S T A B ⟨.keep,.single v,.single w⟩ q)
Hard2OutputGenerationSource.lean:30:      (wholeOutputsMeter S T A B ⟨.keep,.joint v w,.keep⟩ q))
Hard2OutputGenerationSource.lean:31:     (wholeOutputsMeter S T A B ⟨.single v,.keep,.single w⟩ q))
Hard2OutputGenerationSource.lean:32:    (wholeOutputsMeter S T A B ⟨.single v,.single w,.keep⟩ q)
Hard2OutputGenerationSource.lean:33:  | .diagonal v w=>appendOutputsMeter
Hard2OutputGenerationSource.lean:34:    (wholeOutputsMeter S T A B ⟨.keep,.joint v w,.keep⟩ q)
Hard2OutputGenerationSource.lean:35:    (wholeOutputsMeter S T A B ⟨.single v,.keep,.single w⟩ q)
Hard2OutputGenerationSource.lean:36:  | .vertex v=>appendOutputsMeter
Hard2OutputGenerationSource.lean:37:    (wholeOutputsMeter S T A B ⟨.single v,.keep,.keep⟩ q)
Hard2OutputGenerationSource.lean:38:    (wholeOutputsMeter S T A B ⟨.keep,.single v,.keep⟩ q)
Hard2OutputGenerationSource.lean:39:  | .side D=>generatedOutputsMeter S (sideTaggedMeter A B D) q

Hard2OutputGenerationSource.lean:47: def edgeOutputsMeter (S T : Tree) (A B : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (q : Nat) : Charged (List Output) :=
Hard2OutputGenerationSource.lean:48:  let good:=meterRestrictionAgrees S T A
Hard2OutputGenerationSource.lean:49:  let d:=pairDescendantsMeter T e.2
Hard2OutputGenerationSource.lean:50:  let r:=if good.value then kindOutputsMeter (.side d.value) S T A B q
Hard2OutputGenerationSource.lean:51:   else kindOutputsMeter (.side d.value) S T B A q
Hard2OutputGenerationSource.lean:52:  ⟨r.value,good.work+d.work+r.work+8⟩
```

## source-Hard2OutputGenerationSource-hardPaidSource.txt

```text
Hard2OutputGenerationSource.lean:84: def hardPaidSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
Hard2OutputGenerationSource.lean:85:  (T S : Tree) (q : Nat) (c : CherryBranching.Candidate) (out : Result) : SourceExecution :=
Hard2OutputGenerationSource.lean:86:  let os:=actualOutputsMeter S T c q out
Hard2OutputGenerationSource.lean:87:  let r:=fullOutputsSource actual W T S q os.value
Hard2OutputGenerationSource.lean:88:  ⟨r.value,os.work+r.work+4⟩
```

## source-Hard2OutputGenerationSource-sideTaggedMeter.txt

```text
Hard2OutputGenerationSource.lean:8: def sideTaggedMeter (A B D : List Nat) (x : Nat) : Charged Nat :=
Hard2OutputGenerationSource.lean:9:  let a:=meterContains x A
Hard2OutputGenerationSource.lean:10:  if a.value then ⟨0,a.work+5⟩ else
Hard2OutputGenerationSource.lean:11:   let b:=meterContains x B
Hard2OutputGenerationSource.lean:12:   if b.value then let d:=meterContains x D;⟨3*(if d.value then 0 else 1)+1,a.work+b.work+d.work+8⟩
Hard2OutputGenerationSource.lean:13:   else ⟨2,a.work+b.work+7⟩
```

## source-Hard2PairGeometrySource-pairChooseMeter.txt

```text
Hard2PairGeometrySource.lean:97: def pairChooseMeter (T : Tree) (A B : List Nat) : Charged (Option PairGeometry.Choice) :=
Hard2PairGeometrySource.lean:98:  let p:=pairProperMeter T A B
Hard2PairGeometrySource.lean:99:  if p.value then
Hard2PairGeometrySource.lean:100:   let v:=pairVerticesMeter T;let f:=meterFind (pairVertexMeter T A B) v.value
Hard2PairGeometrySource.lean:101:   match f.value with
Hard2PairGeometrySource.lean:102:   | some x=>⟨some (.vertex x),p.work+v.work+f.work+4⟩
Hard2PairGeometrySource.lean:103:   | none=>let e:=pairEdgesMeter T;let g:=meterFind (pairEdgeMeter T A B) e.value
Hard2PairGeometrySource.lean:104:    ⟨g.value.map PairGeometry.Choice.edge,p.work+v.work+f.work+e.work+g.work+4⟩
Hard2PairGeometrySource.lean:105:  else ⟨none,p.work+2⟩
```

## source-Hard2PairGeometrySource-pairDescendantsMeter_pairEdgeMeter_pairEdgesMeter_pairProperMeter_pairVertexMeter_pairVerticesMeter.txt

```text
Hard2PairGeometrySource.lean:7: def pairVerticesMeter (T : Tree) : Charged (List RMAF.Vertex) := meterVertices T

Hard2PairGeometrySource.lean:13: def pairEdgesMeter : Tree→Charged (List (RMAF.Vertex×RMAF.Vertex))
Hard2PairGeometrySource.lean:14:  | .leaf _=>⟨[],1⟩
Hard2PairGeometrySource.lean:15:  | .node l r=>let a:=pairEdgesMeter l;let b:=pairEdgesMeter r
Hard2PairGeometrySource.lean:16:   ⟨([], [false])::([], [true])::
Hard2PairGeometrySource.lean:17:     (a.value.map (fun e=>(false::e.1,false::e.2))++b.value.map (fun e=>(true::e.1,true::e.2))),
Hard2PairGeometrySource.lean:18:    a.work+b.work+12*a.value.length+8*b.value.length+12⟩

Hard2PairGeometrySource.lean:23: def pairProperMeter (T : Tree) (A B : List Nat) : Charged Bool :=
Hard2PairGeometrySource.lean:24:  let l:=meterLeaves T;let nt:=meterNodup l.value;let na:=meterNodup A;let nb:=meterNodup B
Hard2PairGeometrySource.lean:25:  let ca:=meterAll (fun x=>let l:=meterLeaves T;let c:=meterContains x l.value;⟨c.value,l.work+c.work+2⟩) A
Hard2PairGeometrySource.lean:26:  let cb:=meterAll (fun x=>let l:=meterLeaves T;let c:=meterContains x l.value;⟨c.value,l.work+c.work+2⟩) B
Hard2PairGeometrySource.lean:27:  let ab:=meterAll (fun x=>let c:=meterContains x B;⟨!c.value,c.work+2⟩) A
Hard2PairGeometrySource.lean:28:  ⟨nt.value&&na.value&&nb.value&&!A.isEmpty&&!B.isEmpty&&ca.value&&cb.value&&ab.value,
Hard2PairGeometrySource.lean:29:   l.work+nt.work+na.work+nb.work+ca.work+cb.work+ab.work+16⟩

Hard2PairGeometrySource.lean:41: def pairVertexMeter (T : Tree) (A B : List Nat) (v : RMAF.Vertex) : Charged Bool :=
Hard2PairGeometrySource.lean:42:  let a:=meterMinimal A T;let b:=meterMinimal B T
Hard2PairGeometrySource.lean:43:  let ca:=meterVertexContains v a.value;let cb:=meterVertexContains v b.value
Hard2PairGeometrySource.lean:44:  let ra:=pairRegionsMeter A T v;let rb:=pairRegionsMeter B T v
Hard2PairGeometrySource.lean:45:  ⟨ca.value&&cb.value&&(ra.value.length==3||rb.value.length==3),
Hard2PairGeometrySource.lean:46:   a.work+b.work+ca.work+cb.work+ra.work+rb.work+ra.value.length+rb.value.length+12⟩

Hard2PairGeometrySource.lean:57: def pairDescendantsMeter (T : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
Hard2PairGeometrySource.lean:58:  let l:=meterLeaves T
Hard2PairGeometrySource.lean:59:  let d:=meterFilter (fun x=>let a:=meterLeafList [x] T;let p:=pairPrefixMeter v (a.value.headD [])
Hard2PairGeometrySource.lean:60:   ⟨p.value,a.work+p.work+4⟩) l.value
Hard2PairGeometrySource.lean:61:  ⟨d.value,l.work+d.work+2⟩

Hard2PairGeometrySource.lean:87: def pairEdgeMeter (T : Tree) (A B : List Nat) (e : RMAF.Vertex×RMAF.Vertex) : Charged Bool :=
Hard2PairGeometrySource.lean:88:  let a1:=meterMinimal A T;let b1:=meterMinimal B T;let a2:=meterMinimal A T;let b2:=meterMinimal B T
Hard2PairGeometrySource.lean:89:  let ca1:=meterVertexContains e.1 a1.value;let cb1:=meterVertexContains e.1 b1.value
Hard2PairGeometrySource.lean:90:  let ca2:=meterVertexContains e.2 a2.value;let cb2:=meterVertexContains e.2 b2.value
Hard2PairGeometrySource.lean:91:  let sides:=meterAll (pairSideClearMeter T A B e.2) [false,true]
Hard2PairGeometrySource.lean:92:  ⟨ca1.value&&cb1.value&&ca2.value&&cb2.value&&sides.value,
Hard2PairGeometrySource.lean:93:   a1.work+b1.work+a2.work+b2.work+ca1.work+cb1.work+ca2.work+cb2.work+sides.work+8⟩
```

## source-Hard2PairGeometrySource-pairPrefixMeter_pairRegionsMeter_pairSideClearMeter.txt

```text
Hard2PairGeometrySource.lean:34: def pairRegionsMeter (D : List Nat) (T : Tree) (v : RMAF.Vertex) : Charged (List Nat) :=
Hard2PairGeometrySource.lean:35:  meterFilter (fun c=>let l:=meterLeafList D T
Hard2PairGeometrySource.lean:36:   let r:=meterAny (fun a=>let r:=meterRegion v a;⟨r.value==c,r.work+2⟩) l.value
Hard2PairGeometrySource.lean:37:   ⟨r.value,l.work+r.work+2⟩) [0,1,2]

Hard2PairGeometrySource.lean:50: def pairPrefixMeter : RMAF.Vertex→RMAF.Vertex→Charged Bool
Hard2PairGeometrySource.lean:51:  | [],_=>⟨true,2⟩
Hard2PairGeometrySource.lean:52:  | _::_,[]=>⟨false,2⟩
Hard2PairGeometrySource.lean:53:  | s::p,t::a=>let r:=pairPrefixMeter p a;⟨(s==t)&&r.value,r.work+4⟩

Hard2PairGeometrySource.lean:72: def pairSideClearMeter (T : Tree) (A B : List Nat) (v : RMAF.Vertex) (inside : Bool) : Charged Bool :=
Hard2PairGeometrySource.lean:73:  let sa:=pairSideMeter A T v inside;let sb:=pairSideMeter B T v inside
Hard2PairGeometrySource.lean:74:  let sac:=pairSideMeter A T v inside;let sma:=meterMinimal sac.value T;let b:=meterMinimal B T
Hard2PairGeometrySource.lean:75:  let ac:=meterDisjoint sma.value b.value
Hard2PairGeometrySource.lean:76:  let sbc:=pairSideMeter B T v inside;let smb:=meterMinimal sbc.value T;let a:=meterMinimal A T
Hard2PairGeometrySource.lean:77:  let bc:=meterDisjoint smb.value a.value
Hard2PairGeometrySource.lean:78:  ⟨!sa.value.isEmpty&&!sb.value.isEmpty&&ac.value&&bc.value,
Hard2PairGeometrySource.lean:79:   sa.work+sb.work+sac.work+sma.work+b.work+ac.work+sbc.work+smb.work+a.work+bc.work+10⟩
```

## source-Hard2PairGeometrySource-pairSideMeter.txt

```text
Hard2PairGeometrySource.lean:66: def pairSideMeter (A : List Nat) (T : Tree) (v : RMAF.Vertex) (inside : Bool) : Charged (List Nat) :=
Hard2PairGeometrySource.lean:67:  meterFilter (fun x=>let d:=pairDescendantsMeter T v;let c:=meterContains x d.value
Hard2PairGeometrySource.lean:68:   ⟨if inside then c.value else !c.value,d.work+c.work+4⟩) A
```

## source-Hard2RouteSource-Hard2Route_hard2FrontMeter.txt

```text
Hard2RouteSource.lean:10: inductive Hard2Route where
Hard2RouteSource.lean:11:  | refused
Hard2RouteSource.lean:12:  | direct : Option (List (List Nat))→Hard2Route
Hard2RouteSource.lean:13:  | admittedRule5
Hard2RouteSource.lean:14:  | disjointPaid
Hard2RouteSource.lean:15:  | paid : Result→Hard2Route
Hard2RouteSource.lean:16:  deriving Repr

Hard2RouteSource.lean:18: def hard2FrontMeter (T S : Tree) (c : CherryBranching.Candidate) (q : Nat) : Charged Hard2Route :=
Hard2RouteSource.lean:19:  let graph:=runHard2Meter T S c
Hard2RouteSource.lean:20:  match graph.value with
Hard2RouteSource.lean:21:  | none=>⟨.refused,graph.work+2⟩
Hard2RouteSource.lean:22:  | some .disjoint=>
Hard2RouteSource.lean:23:   let p:=partitionMeter S c.a c.b
Hard2RouteSource.lean:24:   let all:=meterAll (meterRestrictionAgrees T S) p.value
Hard2RouteSource.lean:25:   if all.value then
Hard2RouteSource.lean:26:    ⟨.direct (DisjointParents.direct p.value q),graph.work+p.work+all.work+p.value.length+8⟩
Hard2RouteSource.lean:27:   else
Hard2RouteSource.lean:28:    let good:=meterFilter (meterRestrictionAgrees T S) p.value
Hard2RouteSource.lean:29:    ⟨if good.value.length=2 then .admittedRule5 else .disjointPaid,
Hard2RouteSource.lean:30:      graph.work+p.work+all.work+good.work+good.value.length+8⟩
Hard2RouteSource.lean:31:  | some out=>⟨.paid out,graph.work+4⟩
```

## source-Hard2StepTrace-Hard2Receipt.txt

```text
Hard2StepTrace.lean:7: structure Hard2Receipt where
Hard2StepTrace.lean:8:  value : Option (List (List Nat))
Hard2StepTrace.lean:9:  queries : List Query
```

## source-HullCheckMeters-meterDisjoint.txt

```text
HullCheckMeters.lean:5: def meterDisjoint (A B : List RMAF.Vertex) : Charged Bool :=
HullCheckMeters.lean:6:  meterAll (fun v => let c:=meterVertexContains v B;⟨!c.value,c.work+1⟩) A
```

## source-HullCheckMeters-meterHullPair.txt

```text
HullCheckMeters.lean:10: def meterHullPair (T : Tree) (B C : List Nat) : Charged Bool :=
HullCheckMeters.lean:11:  let a:=meterMinimal B T;let b:=meterMinimal C T;let d:=meterDisjoint a.value b.value
HullCheckMeters.lean:12:  ⟨d.value,a.work+b.work+d.work+2⟩
```

## source-HullCheckMeters-meterPairwise.txt

```text
HullCheckMeters.lean:17: def meterPairwise (T : Tree) : Forest → Charged Bool
HullCheckMeters.lean:18:  | []=>⟨true,1⟩
HullCheckMeters.lean:19:  | B::F=>let a:=meterAll (meterHullPair T B) F;let r:=meterPairwise T F
HullCheckMeters.lean:20:          ⟨a.value&&r.value,a.work+r.work+4⟩
```

## source-IncidentWork-incidentAtMeter.txt

```text
IncidentWork.lean:7: def incidentAtMeter (T : Tree) (X : List Nat) (q : RMAF.Vertex) : Measured Bool :=
IncidentWork.lean:8:  if q.isEmpty then ⟨false,1⟩ else
IncidentWork.lean:9:   let m:=minimalMeter X T;let c:=containsAddressMeter q m.value
IncidentWork.lean:10:   let n:=minimalMeter X T;let p:=dropLastMeter q;let d:=containsAddressMeter p.value n.value
IncidentWork.lean:11:   ⟨c.value != d.value,m.work+c.work+n.work+p.work+d.work+4⟩
```

## source-IncidentWork-incidentFilterMeter.txt

```text
IncidentWork.lean:44: def incidentFilterMeter (T : Tree) (X : List Nat) : List RMAF.Vertex→Measured (List RMAF.Vertex)
IncidentWork.lean:45:  | []=>⟨[],1⟩
IncidentWork.lean:46:  | q::qs=>let c:=incidentAtMeter T X q;let r:=incidentFilterMeter T X qs
IncidentWork.lean:47:            ⟨if c.value then q::r.value else r.value,c.work+r.work+2⟩
```

## source-IncidentWork-incidentMeter.txt

```text
IncidentWork.lean:67: def incidentMeter (T : Tree) (X : List Nat) : Measured (List RMAF.Vertex) :=
IncidentWork.lean:68:  let v:=verticesMeter T;let r:=incidentFilterMeter T X v.value
IncidentWork.lean:69:  ⟨r.value,v.work+r.work+1⟩
```

## source-LiteralAtoms-addressListsEqMeter_allMeter_anyMeter_natListEqMeter_treeEqMeter.txt

```text
LiteralAtoms.lean:8: def treeEqMeter : Tree → Tree → Measured Bool
LiteralAtoms.lean:9:  | .leaf x,.leaf y=>⟨decide (x=y),2⟩
LiteralAtoms.lean:10:  | .node a b,.node c d=>
LiteralAtoms.lean:11:    let l:=treeEqMeter a c
LiteralAtoms.lean:12:    if l.value then let r:=treeEqMeter b d;⟨r.value,l.work+r.work+2⟩
LiteralAtoms.lean:13:    else ⟨false,l.work+2⟩
LiteralAtoms.lean:14:  | _,_=>⟨false,1⟩

LiteralAtoms.lean:68: def natListEqMeter := listEqMeter natEqMeter

LiteralAtoms.lean:76: def addressListsEqMeter := listEqMeter eqAddressMeter

LiteralAtoms.lean:86: def anyMeter {α : Type} (f : α→Measured Bool) : List α→Measured Bool
LiteralAtoms.lean:87:  | []=>⟨false,1⟩
LiteralAtoms.lean:88:  | x::xs=>let a:=f x
LiteralAtoms.lean:89:            if a.value then ⟨true,a.work+1⟩
LiteralAtoms.lean:90:            else let r:=anyMeter f xs;⟨r.value,a.work+r.work+1⟩

LiteralAtoms.lean:92: def allMeter {α : Type} (f : α→Measured Bool) : List α→Measured Bool
LiteralAtoms.lean:93:  | []=>⟨true,1⟩
LiteralAtoms.lean:94:  | x::xs=>let a:=f x
LiteralAtoms.lean:95:            if a.value then let r:=allMeter f xs;⟨r.value,a.work+r.work+1⟩
LiteralAtoms.lean:96:            else ⟨false,a.work+1⟩
```

## source-LiteralAtoms-checksMeter.txt

```text
LiteralAtoms.lean:129: def checksMeter : List (Unit→Measured Bool)→Measured Bool
LiteralAtoms.lean:130:  | []=>⟨true,1⟩
LiteralAtoms.lean:131:  | f::fs=>let a:=f ()
LiteralAtoms.lean:132:            if a.value then let r:=checksMeter fs;⟨r.value,a.work+r.work+1⟩
LiteralAtoms.lean:133:            else ⟨false,a.work+1⟩
```

## source-LiteralAtoms-listEqMeter_natEqMeter.txt

```text
LiteralAtoms.lean:37: def listEqMeter {α : Type} (f : α→α→Measured Bool) : List α→List α→Measured Bool
LiteralAtoms.lean:38:  | [],[]=>⟨true,1⟩
LiteralAtoms.lean:39:  | [],_::_=>⟨false,1⟩
LiteralAtoms.lean:40:  | _::_,[]=>⟨false,1⟩
LiteralAtoms.lean:41:  | x::xs,y::ys=>let h:=f x y
LiteralAtoms.lean:42:                  if h.value then let r:=listEqMeter f xs ys;⟨r.value,h.work+r.work+2⟩
LiteralAtoms.lean:43:                  else ⟨false,h.work+2⟩

LiteralAtoms.lean:67: def natEqMeter (x y : Nat) : Measured Bool := ⟨decide (x=y),1⟩
```

## source-LiteralDecision-cutsTwoMeter_notMeter_orMeter.txt

```text
LiteralDecision.lean:6: def notMeter (m : Measured Bool) : Measured Bool := ⟨!m.value,m.work+1⟩

LiteralDecision.lean:7: def orMeter (m : Measured Bool) (f : Unit→Measured Bool) : Measured Bool :=
LiteralDecision.lean:8:  if m.value then ⟨true,m.work+1⟩ else let n:=f ();⟨n.value,m.work+n.work+1⟩

LiteralDecision.lean:18: def cutsTwoMeter (S : Tree) (a b : Nat) : Measured Bool :=
LiteralDecision.lean:19:  let c:=cutsMeter S a b;⟨decide (c.value.length=2),c.work+c.value.length+3⟩
```

## source-LiteralDecision-literalFee.txt

```text
LiteralDecision.lean:63: def literalFee (T S : Tree) (a b : Nat) (j : LiteralCall) : Nat :=
LiteralDecision.lean:64:  (literalMeter T S a b j.selection j.u j.v j.row j.core j.qa j.ub).work
```

## source-LiteralDecision-literalMeter.txt

```text
LiteralDecision.lean:47: def literalMeter (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
LiteralDecision.lean:48:  (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : Measured Bool :=
LiteralDecision.lean:49:  checksMeter (literalChecks T S a b d u v R C qa ub)
```

## source-LiteralScheduleReceiptSource-LiteralReceiptSource_literalRunSource.txt

```text
LiteralScheduleReceiptSource.lean:4: structure LiteralReceiptSource (P A : Type) where
LiteralScheduleReceiptSource.lean:5:  value : MeterReceipt P A
LiteralScheduleReceiptSource.lean:6:  localWork : Nat
LiteralScheduleReceiptSource.lean:7:  callbackWork : Nat

LiteralScheduleReceiptSource.lean:9: def literalRunSource {P A : Type} (f : P→Nat→Charged (Option (Nat×A))) (b : Nat) :
LiteralScheduleReceiptSource.lean:10:  List (Job P A)→LiteralReceiptSource P A
LiteralScheduleReceiptSource.lean:11:  | []=>⟨⟨⟨some [],[],0⟩,[],2,0⟩,2,0⟩
LiteralScheduleReceiptSource.lean:12:  | .resolved _ c a::js=>let r:=literalRunSource f b js
LiteralScheduleReceiptSource.lean:13:    ⟨⟨⟨r.value.value.answers.map ((c,a)::·),r.value.value.calls,r.value.value.visits+1⟩,
LiteralScheduleReceiptSource.lean:14:      r.value.queries,r.value.callerWork+5,r.value.recursiveWork⟩,r.localWork+32,r.callbackWork⟩
LiteralScheduleReceiptSource.lean:15:  | .hard p::js=>let a:=f p b
LiteralScheduleReceiptSource.lean:16:    match a.value with
LiteralScheduleReceiptSource.lean:17:    | none=>⟨⟨⟨none,[b],1⟩,[(p,b)],8,0⟩,32,a.work⟩
LiteralScheduleReceiptSource.lean:18:    | some x=>let r:=literalRunSource f b js
LiteralScheduleReceiptSource.lean:19:      ⟨⟨⟨r.value.value.answers.map (x::·),b::r.value.value.calls,r.value.value.visits+1⟩,
LiteralScheduleReceiptSource.lean:20:        (p,b)::r.value.queries,r.value.callerWork+8,r.value.recursiveWork⟩,
LiteralScheduleReceiptSource.lean:21:        r.localWork+32,a.work+r.callbackWork⟩
```

## source-LiteralScheduleReceiptSource-literalScheduleSource.txt

```text
LiteralScheduleReceiptSource.lean:44: def literalScheduleSource {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
LiteralScheduleReceiptSource.lean:45:  (q : Nat) (js : List (Job P A)) : LiteralReceiptSource P A:=
LiteralScheduleReceiptSource.lean:46:  let k:=knownCostMeter js;let p:=pendingMeter js
LiteralScheduleReceiptSource.lean:47:  if q<k.value+2*p.value then
LiteralScheduleReceiptSource.lean:48:   ⟨⟨⟨none,[],0⟩,[],8*js.length+8,0⟩,k.work+p.work+js.length+24,0⟩ else
LiteralScheduleReceiptSource.lean:49:  let b:=allocatedMeter q js;let r:=literalRunSource f b.value js
LiteralScheduleReceiptSource.lean:50:  let a:=acceptAnswersMeter q r.value.value.answers
LiteralScheduleReceiptSource.lean:51:  let pc:=postChargeMeter r.value.value
LiteralScheduleReceiptSource.lean:52:  ⟨⟨⟨a.value,r.value.value.calls,r.value.value.visits⟩,r.value.queries,
LiteralScheduleReceiptSource.lean:53:      16*js.length+20+r.value.callerWork+pc.value,r.value.recursiveWork⟩,
LiteralScheduleReceiptSource.lean:54:    k.work+p.work+b.work+r.localWork+a.work+pc.work+js.length+40,r.callbackWork⟩
```

## source-LiteralStructural-atTreeMeter_boundaryEqMeter_cherryExistsMeter_incidentEqMeter_labelsMeter_minimalMemMeter_tailMemMeter.txt

```text
LiteralStructural.lean:7: def atTreeMeter (T : Tree) (q : RMAF.Vertex) (U : Tree) : Measured Bool :=
LiteralStructural.lean:8:  let s:=subtreeMeter T q
LiteralStructural.lean:9:  match s.value with
LiteralStructural.lean:10:  | none=>⟨false,s.work+2⟩
LiteralStructural.lean:11:  | some V=>let e:=treeEqMeter U V;⟨e.value,s.work+e.work+2⟩

LiteralStructural.lean:44: def cherryExistsMeter (T : Tree) (a b : Nat) : Measured Bool :=
LiteralStructural.lean:45:  let v:=verticesMeter T;let z:=anyMeter (cherryAtEitherMeter T a b) v.value
LiteralStructural.lean:46:  ⟨z.value,v.work+z.work+1⟩

LiteralStructural.lean:84: def labelsMeter (T C X : Tree) (c : Nat) : Measured Bool :=
LiteralStructural.lean:85:  let l:=leavesMeter T;let z:=allMeter (labelPointMeter C X c) l.value
LiteralStructural.lean:86:  ⟨z.value,l.work+z.work+1⟩

LiteralStructural.lean:104: def incidentEqMeter (T X : Tree) (u v : RMAF.Vertex) : Measured Bool :=
LiteralStructural.lean:105:  let x:=leavesMeter X;let i:=incidentMeter T x.value
LiteralStructural.lean:106:  let e:=addressListsEqMeter [v,u] i.value
LiteralStructural.lean:107:  ⟨e.value,x.work+i.work+e.work+3⟩

LiteralStructural.lean:114: def minimalMemMeter (T X : Tree) (q : RMAF.Vertex) : Measured Bool :=
LiteralStructural.lean:115:  let x:=leavesMeter X;let m:=minimalMeter x.value T;let c:=containsAddressMeter q m.value
LiteralStructural.lean:116:  ⟨c.value,x.work+m.work+c.work+2⟩

LiteralStructural.lean:123: def tailMemMeter (T X : Tree) (q : RMAF.Vertex) : Measured Bool :=
LiteralStructural.lean:124:  let d:=dropLastMeter q;let m:=minimalMemMeter T X d.value
LiteralStructural.lean:125:  ⟨m.value,d.work+m.work+1⟩

LiteralStructural.lean:131: def boundaryEqMeter (S X : Tree) (p : RMAF.Vertex) : Measured Bool :=
LiteralStructural.lean:132:  let s:=subtreeLabelsMeter S p;let x:=leavesMeter X;let e:=natListEqMeter s.value x.value
LiteralStructural.lean:133:  ⟨e.value,s.work+x.work+e.work+2⟩
```

## source-LiteralStructural-cherryAtEitherMeter_labelPointMeter.txt

```text
LiteralStructural.lean:27: def cherryAtEitherMeter (T : Tree) (a b : Nat) (q : RMAF.Vertex) : Measured Bool :=
LiteralStructural.lean:28:  let x:=atTreeMeter T q (.node (.leaf a) (.leaf b))
LiteralStructural.lean:29:  if x.value then ⟨true,x.work+1⟩
LiteralStructural.lean:30:  else let y:=atTreeMeter T q (.node (.leaf b) (.leaf a));⟨y.value,x.work+y.work+1⟩

LiteralStructural.lean:65: def labelPointMeter (C X : Tree) (c z : Nat) : Measured Bool :=
LiteralStructural.lean:66:  let lc:=leavesMeter C;let lx:=leavesMeter X
LiteralStructural.lean:67:  let mc:=containsMeter z lc.value;let mx:=containsMeter z lx.value
LiteralStructural.lean:68:  ⟨decide (mc.value=(!mx.value && decide (z≠c))),lc.work+lx.work+mc.work+mx.work+4⟩
```

## source-LocalSelector-LocalSelection.txt

```text
LocalSelector.lean:5: inductive LocalSelection where
LocalSelector.lean:6:  | large (e : RMAF.Vertex)
LocalSelector.lean:7:  | two (c : SizeTwoSelection)
LocalSelector.lean:8:  | outside (c : OutsideSelection)
LocalSelector.lean:9:  | remaining
LocalSelector.lean:10:  deriving Repr, DecidableEq
```

## source-Marked-marked.txt

```text
Marked.lean:7: def marked (t : Tree) (X : List Nat) (y rho : Nat) : Option Tree :=
Marked.lean:8:   (restrict (y::X) t).map (relabel (swap y rho))
```

## source-MergeEnumeration-mergeMeter.txt

```text
MergeEnumeration.lean:61: def mergeMeter (X Y : List Nat) (x y rho gamma : Nat) (FM FN : Forest) : Measured (List Forest) :=
MergeEnumeration.lean:62:  let GM:=relabelForest (swap y rho) FM
MergeEnumeration.lean:63:  let GN:=relabelForest (swap x gamma) FN
MergeEnumeration.lean:64:  let r:=ownersMeter X Y GM GN GM
MergeEnumeration.lean:65:  ⟨r.value,2*cells FM+2*cells FN+r.work⟩
```

## source-MergeEnumeration-ownersMeter.txt

```text
MergeEnumeration.lean:10: def ownersMeter (X Y : List Nat) (GM GN : Forest) : Forest→Measured (List Forest)
MergeEnumeration.lean:11:  | [] => ⟨[],1⟩
MergeEnumeration.lean:12:  | H::hs => let p:=rowMeter X Y GM GN H GN;let r:=ownersMeter X Y GM GN hs
MergeEnumeration.lean:13:             ⟨p.value++r.value,p.work+r.work+p.value.length+1⟩
```

## source-MergeEnumeration-rowMeter.txt

```text
MergeEnumeration.lean:5: def rowMeter (X Y : List Nat) (GM GN : Forest) (H : List Nat) : Forest→Measured (List Forest)
MergeEnumeration.lean:6:  | [] => ⟨[],1⟩
MergeEnumeration.lean:7:  | J::js => let p:=pairMeter X Y GM GN H J;let r:=rowMeter X Y GM GN H js
MergeEnumeration.lean:8:             ⟨p.value::r.value,p.work+r.work+1⟩
```

## source-MergeOperations-Measured.txt

```text
MergeOperations.lean:4: structure Measured (α : Type) where
MergeOperations.lean:5:  value : α
MergeOperations.lean:6:  work : Nat
MergeOperations.lean:7:  deriving Repr
```

## source-MergeOperations-eraseMeter_filterMeter.txt

```text
MergeOperations.lean:12: def filterMeter (X : List Nat) : List Nat→Measured (List Nat)
MergeOperations.lean:13:  | [] => ⟨[],1⟩
MergeOperations.lean:14:  | x::xs => let r:=filterMeter X xs
MergeOperations.lean:15:             ⟨if X.contains x then x::r.value else r.value,X.length+2+r.work⟩

MergeOperations.lean:29: def eraseMeter (H : List Nat) : Forest→Measured Forest
MergeOperations.lean:30:  | [] => ⟨[],1⟩
MergeOperations.lean:31:  | B::F => if H==B then ⟨F,H.length+B.length+2⟩
MergeOperations.lean:32:            else let r:=eraseMeter H F
MergeOperations.lean:33:                 ⟨B::r.value,H.length+B.length+2+r.work⟩
```

## source-MergeOperations-pairMeter.txt

```text
MergeOperations.lean:55: def pairMeter (X Y : List Nat) (GM GN : Forest) (H J : List Nat) : Measured Forest :=
MergeOperations.lean:56:  let K:=filterMeter X H;let L:=filterMeter Y J
MergeOperations.lean:57:  let FX:=eraseMeter H GM;let FY:=eraseMeter J GN
MergeOperations.lean:58:  ⟨merged K.value L.value FX.value FY.value,
MergeOperations.lean:59:  K.work+L.work+FX.work+FY.work+K.value.length+FX.value.length+1⟩
```

## source-MeterErase-Query.txt

```text
MeterErase.lean:28: abbrev Query := (Tree × Tree) × Nat
```

## source-OWRecovery-meterInputCheck.txt

```text
OWRecovery.lean:7: def meterInputCheck (S : Tree) (P : CommonForest) : Charged Bool :=
OWRecovery.lean:8:  let a:=meterLeaves S;let n:=meterNodup a.value
OWRecovery.lean:9:  let b:=meterLeaves S;let p:=meterPartition b.value P
OWRecovery.lean:10:  let e:=meterPairwise S P
OWRecovery.lean:11:  ⟨n.value&&p.value&&e.value,a.work+n.work+b.work+p.work+e.work+8⟩
```

## source-OWScan-ScanMeasured.txt

```text
OWScan.lean:34: structure ScanMeasured where
OWScan.lean:35:  value : Scan
OWScan.lean:36:  work : Nat
OWScan.lean:37:  administration : Nat
```

## source-OWScan-meterLength.txt

```text
OWScan.lean:8: def meterLength {α : Type} : List α→Charged Nat
OWScan.lean:9:  | []=>⟨0,2⟩
OWScan.lean:10:  | _::xs=>let r:=meterLength xs;⟨r.value+1,r.work+4⟩
```

## source-Ordinary-cuts.txt

```text
Ordinary.lean:6: def cuts (S : Tree) (a b : Nat) := pendantOriginal S a b
```

## source-OrdinaryPrepareSource-ordinaryPrepareMeter.txt

```text
OrdinaryPrepareSource.lean:41: def ordinaryPrepareMeter (T S : Tree) : List (List Nat)→Charged (Option (List (Job (List Nat) (List (List Nat)))))
OrdinaryPrepareSource.lean:42:  | []=>⟨some [],2⟩
OrdinaryPrepareSource.lean:43:  | U::Q=>let s:=ordinarySlotMeter T S U;let r:=ordinaryPrepareMeter T S Q
OrdinaryPrepareSource.lean:44:            ⟨s.value.bind (fun j=>r.value.map (j::·)),s.work+r.work+8⟩
```

## source-OrdinaryPrepareSource-ordinarySlotMeter.txt

```text
OrdinaryPrepareSource.lean:16: def ordinarySlotMeter (T S : Tree) (U : List Nat) : Charged (Option (Job (List Nat) (List (List Nat)))):=
OrdinaryPrepareSource.lean:17:  let p:=properBlockMeter T S U
OrdinaryPrepareSource.lean:18:  if !p.value then ⟨none,p.work+6⟩ else
OrdinaryPrepareSource.lean:19:   let t:=meterRestrict U T;let s:=meterRestrict U S
OrdinaryPrepareSource.lean:20:   match t.value,s.value with
OrdinaryPrepareSource.lean:21:   | some t',some s'=>
OrdinaryPrepareSource.lean:22:    let pre:=meterPretest t' s'
OrdinaryPrepareSource.lean:23:    match pre.value with
OrdinaryPrepareSource.lean:24:    | .refused=>⟨none,p.work+t.work+s.work+pre.work+12⟩
OrdinaryPrepareSource.lean:25:    | .rejected=>⟨some (.hard U),p.work+t.work+s.work+pre.work+12⟩
OrdinaryPrepareSource.lean:26:    | .found c=>let f:=meterForest s' c
OrdinaryPrepareSource.lean:27:                ⟨some (.resolved U (DepthOne.cutCost c) f.value),p.work+t.work+s.work+pre.work+f.work+16⟩
OrdinaryPrepareSource.lean:28:   | _,_=>⟨none,p.work+t.work+s.work+10⟩
```

## source-OrdinaryPrepareSource-properBlockMeter.txt

```text
OrdinaryPrepareSource.lean:7: def properBlockMeter (T S : Tree) (U : List Nat) : Charged Bool:=
OrdinaryPrepareSource.lean:8:  let n:=meterNodup U
OrdinaryPrepareSource.lean:9:  let all:=meterAll (fun x=>let t:=meterLeaves T;let s:=meterLeaves S
OrdinaryPrepareSource.lean:10:   let a:=meterContains x t.value;let b:=meterContains x s.value
OrdinaryPrepareSource.lean:11:   ⟨a.value&&b.value,t.work+s.work+a.work+b.work+4⟩) U
OrdinaryPrepareSource.lean:12:  ⟨n.value && !U.isEmpty && all.value,n.work+all.work+8⟩
```

## source-OrdinarySchedulerSource-answerFlattenMeter.txt

```text
OrdinarySchedulerSource.lean:39: def answerFlattenMeter : List (Nat×List (List Nat))→Charged (List (List Nat))
OrdinarySchedulerSource.lean:40:  | []=>⟨[],2⟩
OrdinarySchedulerSource.lean:41:  | x::xs=>let r:=answerFlattenMeter xs
OrdinarySchedulerSource.lean:42:    ⟨x.2++r.value,2*x.2.length+r.work+12⟩
```

## source-OrdinarySchedulerSource-mafRecursiveMeter_optionFlattenMeter_ordinaryQueriesMeter.txt

```text
OrdinarySchedulerSource.lean:9: def mafRecursiveMeter (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
OrdinarySchedulerSource.lean:10:  (U : List Nat) (b : Nat) : Charged (Option (Nat×List (List Nat))):=
OrdinarySchedulerSource.lean:11:  let t:=meterRestrict U T;let s:=meterRestrict U S
OrdinarySchedulerSource.lean:12:  match t.value,s.value with
OrdinarySchedulerSource.lean:13:  | some t',some s'=>let a:=GenericForest.solve actual (some t') [s'] b
OrdinarySchedulerSource.lean:14:    ⟨a.map (fun F=>(F.length-1,F)),t.work+s.work+(a.map List.length).getD 0+12⟩
OrdinarySchedulerSource.lean:15:  | _,_=>⟨none,t.work+s.work+8⟩

OrdinarySchedulerSource.lean:24: def ordinaryQueriesMeter (T S : Tree) : List (List Nat×Nat)→Charged (List Call)
OrdinarySchedulerSource.lean:25:  | []=>⟨[],2⟩
OrdinarySchedulerSource.lean:26:  | ub::qs=>let t:=meterRestrict ub.1 T;let s:=meterRestrict ub.1 S
OrdinarySchedulerSource.lean:27:    let r:=ordinaryQueriesMeter T S qs
OrdinarySchedulerSource.lean:28:    ⟨(match t.value,s.value with
OrdinarySchedulerSource.lean:29:       | some t',some s'=>some (⟨some t',[s'],ub.2⟩:Call)
OrdinarySchedulerSource.lean:30:       | _,_=>none).toList++r.value,t.work+s.work+r.work+12⟩

OrdinarySchedulerSource.lean:46: def optionFlattenMeter (o : Option (List (Nat×List (List Nat)))) : Charged (Option (List (List Nat))):=
OrdinarySchedulerSource.lean:47:  match o with
OrdinarySchedulerSource.lean:48:  | none=>⟨none,2⟩
OrdinarySchedulerSource.lean:49:  | some xs=>let f:=answerFlattenMeter xs;⟨some f.value,f.work+4⟩
```

## source-OrdinarySchedulerSource-ordinaryLocalSource.txt

```text
OrdinarySchedulerSource.lean:54: def ordinaryLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
OrdinarySchedulerSource.lean:55:  (Q : List (List Nat)) (b : Nat) : SourceExecution:=
OrdinarySchedulerSource.lean:56:  let prep:=ordinaryPrepareMeter T S Q
OrdinarySchedulerSource.lean:57:  match prep.value with
OrdinarySchedulerSource.lean:58:  | none=>⟨⟨none,[]⟩,prep.work+4⟩
OrdinarySchedulerSource.lean:59:  | some js=>let r:=scheduleSourceMeter (mafRecursiveMeter actual T S) b js
OrdinarySchedulerSource.lean:60:    let f:=optionFlattenMeter r.value.answers
OrdinarySchedulerSource.lean:61:    let qs:=ordinaryQueriesMeter T S r.queries
OrdinarySchedulerSource.lean:62:    ⟨⟨f.value,qs.value⟩,prep.work+r.callerWork+r.recursiveWork+f.work+qs.work+16⟩
```

## source-OriginalSides-OriginalSplit.txt

```text
OriginalSides.lean:39: def OriginalSplit (T : Tree) (X Y : List Nat) : Prop :=
OriginalSides.lean:40:   ∃ p u, p≠[] ∧ subtree T p=some u ∧ ((leaves u).Perm Y ∨ (leaves u).Perm X)
```

## source-OutputDefs-sourceForest.txt

```text
OutputDefs.lean:9: def sourceForest (S : Tree) (Q : List (List Nat)) : List Tree :=
OutputDefs.lean:10:   Q.filterMap (fun U => restrict U S)
```

## source-OutputRun-OutputResult.trace.txt

```text
OutputRun.lean:28: def OutputResult.trace : OutputResult → List (Problem × Nat)
OutputRun.lean:29:  | .scheduled r => r.queries
OutputRun.lean:30:  | _ => []
```

## source-OutputRun-OutputResult.txt

```text
OutputRun.lean:7: inductive OutputResult where
OutputRun.lean:8:  | unaffordable
OutputRun.lean:9:  | refused
OutputRun.lean:10:  | scheduled (receipt : MeterReceipt Problem Forest)
```

## source-OutsideClassifierWork-coreCheckMeter_coreContainsMeter.txt

```text
OutsideClassifierWork.lean:5: def coreCheckMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt Bool :=
OutsideClassifierWork.lean:6:  let c:=coreMeter S a b;let r:=checkMeter fee (.restriction T S c.value)
OutsideClassifierWork.lean:7:  ⟨r.value,c.work+r.work+1,r.calls⟩

OutsideClassifierWork.lean:9: def coreContainsMeter (S : Tree) (a b x : Nat) : Measured Bool :=
OutsideClassifierWork.lean:10:  let c:=coreMeter S a b;let r:=containsMeter x c.value
OutsideClassifierWork.lean:11:  ⟨r.value,c.work+r.work+1⟩
```

## source-OutsideClassifierWork-outsideAtMeter.txt

```text
OutsideClassifierWork.lean:19: def outsideAtMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) (c : CherryRow) : CheckReceipt (Option OutsideSelection) :=
OutsideClassifierWork.lean:20:  let (j,p,q):=c;let r:=andSequence (outsideGuards fee T S a b p q)
OutsideClassifierWork.lean:21:  ⟨if r.value then some ⟨j,p,q⟩ else none,r.work+4,r.calls⟩
```

## source-OutsideClassifierWork-outsideGuards.txt

```text
OutsideClassifierWork.lean:13: def outsideGuards (fee : CheckRequest→Nat) (T S : Tree) (a b p q : Nat) : List (Unit→CheckReceipt Bool) :=
OutsideClassifierWork.lean:14:  [fun _=>coreCheckMeter fee T S a b,
OutsideClassifierWork.lean:15:   fun _=>liftMeter (coreContainsMeter S a b p),fun _=>liftMeter (coreContainsMeter S a b q),
OutsideClassifierWork.lean:16:   fun _=>liftMeter ⟨p != a,1⟩,fun _=>liftMeter ⟨p != b,1⟩,
OutsideClassifierWork.lean:17:   fun _=>liftMeter ⟨q != a,1⟩,fun _=>liftMeter ⟨q != b,1⟩]
```

## source-OutsideClassifierWork-selectOutsideMeter.txt

```text
OutsideClassifierWork.lean:83: def selectOutsideMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option OutsideSelection) :=
OutsideClassifierWork.lean:84:  optionsHeadMeter (cherriesMeter S) (outsideAtMeter fee T S a b)
```

## source-OutsideCore-OutsideSelection.txt

```text
OutsideCore.lean:109: structure OutsideSelection where
OutsideCore.lean:110:  parent : RMAF.Vertex
OutsideCore.lean:111:  p : Nat
OutsideCore.lean:112:  q : Nat
OutsideCore.lean:113:  deriving Repr, DecidableEq
```

## source-OverlapDefs-Order.txt

```text
OverlapDefs.lean:10: inductive Order where
OverlapDefs.lean:11:  | abc | acb | bac | bca
OverlapDefs.lean:12:  deriving DecidableEq,Repr
```

## source-OverlapDefs-Result_first_second_third.txt

```text
OverlapDefs.lean:13: def first (o : Order) (A B C : List Nat) : List Nat :=
OverlapDefs.lean:14:  match o with | .abc => A | .acb => A | .bac => B | .bca => B

OverlapDefs.lean:15: def second (o : Order) (A B C : List Nat) : List Nat :=
OverlapDefs.lean:16:  match o with | .abc => B | .acb => C | .bac => A | .bca => C

OverlapDefs.lean:17: def third (o : Order) (A B C : List Nat) : List Nat :=
OverlapDefs.lean:18:  match o with | .abc => C | .acb => B | .bac => C | .bca => A

OverlapDefs.lean:33: inductive Result where
OverlapDefs.lean:34:  | disjoint
OverlapDefs.lean:35:  | clique : RMAF.Vertex → Result
OverlapDefs.lean:36:  | four : Order → RMAF.Vertex → RMAF.Vertex → Result
OverlapDefs.lean:37:  | diagonal : Order → RMAF.Vertex → RMAF.Vertex → Result
OverlapDefs.lean:38:  | pair : Order → PairGeometry.Choice → Result
OverlapDefs.lean:39:  deriving DecidableEq,Repr
```

## source-OwnerCost-meterLabels.txt

```text
OwnerCost.lean:5: def meterLabels : Tree→Charged (List Nat)
OwnerCost.lean:6:  | .leaf x => ⟨[x],4⟩
OwnerCost.lean:7:  | .node l r =>
OwnerCost.lean:8:   let a := meterLabels l
OwnerCost.lean:9:   let b := meterLabels r
OwnerCost.lean:10:   ⟨a.value++b.value,a.work+b.work+4*(a.value.length+1)+4⟩
```

## source-OwnerCost-meterOwner.txt

```text
OwnerCost.lean:36: def meterOwner (x : Nat) : List Tree→Charged Nat
OwnerCost.lean:37:  | [] => ⟨0,4⟩
OwnerCost.lean:38:  | s::ss =>
OwnerCost.lean:39:   let ls := meterLabels s
OwnerCost.lean:40:   let m := meterContains x ls.value
OwnerCost.lean:41:   if m.value then ⟨0,ls.work+m.work+8⟩ else
OwnerCost.lean:42:    let r := meterOwner x ss
OwnerCost.lean:43:    ⟨r.value+1,ls.work+m.work+r.work+8⟩
```

## source-PaidAddresses-findLeafMeter.txt

```text
PaidAddresses.lean:22: def findLeafMeter (T : Tree) (a : Nat) : List RMAF.Vertex→Measured (Option RMAF.Vertex)
PaidAddresses.lean:23:  | []=>⟨none,1⟩
PaidAddresses.lean:24:  | q::qs=>let h:=leafAtMeter T q a
PaidAddresses.lean:25:            if h.value then ⟨some q,h.work+2⟩ else
PaidAddresses.lean:26:             let r:=findLeafMeter T a qs;⟨r.value,h.work+r.work+2⟩
```

## source-PaidAddresses-leafAddressMeter.txt

```text
PaidAddresses.lean:44: def leafAddressMeter (T : Tree) (a : Nat) : Measured (Option RMAF.Vertex) :=
PaidAddresses.lean:45:  let vs:=verticesMeter T;let r:=findLeafMeter T a vs.value
PaidAddresses.lean:46:  ⟨r.value,vs.work+r.work+1⟩
```

## source-PaidAddresses-leafAtMeter.txt

```text
PaidAddresses.lean:5: def leafAtMeter (T : Tree) (q : RMAF.Vertex) (a : Nat) : Measured Bool :=
PaidAddresses.lean:6:  let s:=subtreeMeter T q
PaidAddresses.lean:7:  match s.value with
PaidAddresses.lean:8:  | none=>⟨false,s.work+2⟩
PaidAddresses.lean:9:  | some U=>let e:=leafEqMeter U a;⟨e.value,s.work+e.work+2⟩
```

## source-PaidArcPartition-arcFromMeter.txt

```text
PaidArcPartition.lean:86: def arcFromMeter (T : Tree) : List RMAF.Vertex→List (List Nat)→Charged (List (List Nat))
PaidArcPartition.lean:87:  | [],P=>⟨P,1⟩
PaidArcPartition.lean:88:  | q::qs,P=>let x:=meterSubtreeLabels T q;let s:=splitForestMeter x.value P
PaidArcPartition.lean:89:              let r:=arcFromMeter T qs s.value
PaidArcPartition.lean:90:              ⟨r.value,x.work+s.work+r.work+3⟩
```

## source-PaidArcPartition-arcPartitionMeter.txt

```text
PaidArcPartition.lean:96: def arcPartitionMeter (T : Tree) (qs : List RMAF.Vertex) : Charged (List (List Nat)) :=
PaidArcPartition.lean:97:  let l:=meterLeaves T;let r:=arcFromMeter T qs [l.value];⟨r.value,l.work+r.work+3⟩
```

## source-PaidArcPartition-splitBlockMeter.txt

```text
PaidArcPartition.lean:9: def splitBlockMeter (X B : List Nat) : Charged (List (List Nat)) :=
PaidArcPartition.lean:10:  let y:=meterFilter (fun x=>meterContains x X) B
PaidArcPartition.lean:11:  let n:=meterFilter (fun x=>let a:=meterContains x X;⟨!a.value,a.work+1⟩) B
PaidArcPartition.lean:12:  let f:=meterFilter (fun C:List Nat=>⟨!C.isEmpty,2⟩) [y.value,n.value]
PaidArcPartition.lean:13:  ⟨f.value,y.work+n.work+f.work+5⟩
```

## source-PaidArcPartition-splitForestMeter.txt

```text
PaidArcPartition.lean:19: def splitForestMeter (X : List Nat) : List (List Nat)→Charged (List (List Nat))
PaidArcPartition.lean:20:  | []=>⟨[],1⟩
PaidArcPartition.lean:21:  | B::P=>let a:=splitBlockMeter X B;let r:=splitForestMeter X P
PaidArcPartition.lean:22:           ⟨a.value++r.value,a.work+r.work+a.value.length+3⟩
```

## source-PaidBestSource-bestForMeter.txt

```text
PaidBestSource.lean:14: def bestForMeter (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : PaidExecutionReceipt (Option Forest) :=
PaidBestSource.lean:15:  let a:=answersMeter cb W R q
PaidBestSource.lean:16:  let b:=bestLengthMeter (originalAcceptedMeter T S q) a.value
PaidBestSource.lean:17:  ⟨b.value,a.prefixWork+b.work+a.value.length+2,a.forestDebit,a.ordinaryCalls⟩
```

## source-PaidBestSource-originalAcceptedMeter.txt

```text
PaidBestSource.lean:8: def originalAcceptedMeter (T S : Tree) (q : Nat) (F : Forest) : Measured Bool :=
PaidBestSource.lean:9:  let a:=measuredAgreement T S F;⟨a.value&&decide (F.length-1≤q),a.work+F.length+3⟩
```

## source-PaidBestSource-paidSelectedSource.txt

```text
PaidBestSource.lean:59: def paidSelectedSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
PaidBestSource.lean:60:  (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : Charged Rule5PaidOrdinary.SelectedResult :=
PaidBestSource.lean:61:  let r:=solveSelectedMeter cb W classFee literalFee T S a b q;⟨r.value,r.prefixWork+r.forestDebit⟩
```

## source-PaidBestSource-solveSelectedMeter.txt

```text
PaidBestSource.lean:30: def solveSelectedMeter (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
PaidBestSource.lean:31:  (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : PaidExecutionReceipt Rule5PaidOrdinary.SelectedResult :=
PaidBestSource.lean:32:  let p:=paidSelectedMeter classFee literalFee T S a b
PaidBestSource.lean:33:  match p.value with
PaidBestSource.lean:34:  | none=>⟨.builderRefused,p.work+2,0,[]⟩
PaidBestSource.lean:35:  | some R=>
PaidBestSource.lean:36:   let r:=bestForMeter cb W R q
PaidBestSource.lean:37:   ⟨.answered r.value,p.work+r.prefixWork+2,r.forestDebit,r.ordinaryCalls⟩
```

## source-PaidBuilderOuter-LiteralCall.txt

```text
PaidBuilderOuter.lean:5: structure LiteralCall where
PaidBuilderOuter.lean:6:  row : BottomData
PaidBuilderOuter.lean:7:  core : Tree
PaidBuilderOuter.lean:8:  qa : RMAF.Vertex
PaidBuilderOuter.lean:9:  ub : RMAF.Vertex
PaidBuilderOuter.lean:10:  selection : BadSelection
PaidBuilderOuter.lean:11:  u : RMAF.Vertex
PaidBuilderOuter.lean:12:  v : RMAF.Vertex
PaidBuilderOuter.lean:13:  deriving DecidableEq, Repr
```

## source-PaidBuilderOuter-buildOneMeter_findBuilderMeter.txt

```text
PaidBuilderOuter.lean:22: def buildOneMeter (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
PaidBuilderOuter.lean:23:  (u v : RMAF.Vertex) (R : BottomData) : Measured (Option (LiteralGeometry T S)) :=
PaidBuilderOuter.lean:24:  bump ((subtreeMeter T v).work+(leafAddressMeter T R.a).work+(leafAddressMeter T R.b).work+5) <|
PaidBuilderOuter.lean:25:  match hc:subtree T v,leafAddress? T R.a,leafAddress? T R.b with
PaidBuilderOuter.lean:26:  | some C,some qa,some ub=>
PaidBuilderOuter.lean:27:    bump (fee ⟨R,C,qa,ub,d,u,v⟩+1) <|
PaidBuilderOuter.lean:28:    if h:LiteralProps T S a b d u v R C qa ub then ⟨some (ofProps hc h),1⟩ else ⟨none,1⟩
PaidBuilderOuter.lean:29:  | _,_,_=>⟨none,1⟩

PaidBuilderOuter.lean:92: def findBuilderMeter {α β : Type} (f : α→Measured (Option β)) : List α→Measured (Option β)
PaidBuilderOuter.lean:93:  | []=>⟨none,1⟩
PaidBuilderOuter.lean:94:  | x::xs=>let a:=f x
PaidBuilderOuter.lean:95:            match a.value with
PaidBuilderOuter.lean:96:            | some y=>⟨some y,a.work+2⟩
PaidBuilderOuter.lean:97:            | none=>let r:=findBuilderMeter f xs;⟨r.value,a.work+r.work+2⟩
```

## source-PaidBuilderOuter-secondBuilderMeter.txt

```text
PaidBuilderOuter.lean:115: def secondBuilderMeter (fee : LiteralCall→Nat) (T S : Tree) (a b : Nat) (d : BadSelection)
PaidBuilderOuter.lean:116:  (u v : RMAF.Vertex) : Measured (Option (LiteralGeometry T S)) :=
PaidBuilderOuter.lean:117:  let rs:=rowsMeter S a b d.c
PaidBuilderOuter.lean:118:  let out:=findBuilderMeter (buildOneMeter fee T S a b d u v) rs.value
PaidBuilderOuter.lean:119:  ⟨out.value,rs.work+out.work+1⟩
```

## source-PaidCaller-LiteralGeometry.txt

```text
PaidCaller.lean:10: structure LiteralGeometry (T S : Tree) where
PaidCaller.lean:11:  X : Tree
PaidCaller.lean:12:  C : Tree
PaidCaller.lean:13:  w : RMAF.Vertex
PaidCaller.lean:14:  r : RMAF.Vertex
PaidCaller.lean:15:  qa : RMAF.Vertex
PaidCaller.lean:16:  ub : RMAF.Vertex
PaidCaller.lean:17:  uc : RMAF.Vertex
PaidCaller.lean:18:  sa : Bool
PaidCaller.lean:19:  sc : Bool
PaidCaller.lean:20:  sb : Bool
PaidCaller.lean:21:  a : Nat
PaidCaller.lean:22:  b : Nat
PaidCaller.lean:23:  c : Nat
PaidCaller.lean:24:  properT : (leaves T).Nodup
PaidCaller.lean:25:  properS : (leaves S).Nodup
PaidCaller.lean:26:  same : ∀ x, x ∈ leaves T ↔ x ∈ leaves S
PaidCaller.lean:27:  source : subtree S w = some (bottom sa sc sb a b c X)
PaidCaller.lean:28:  cherry : ActualCherry T a b
PaidCaller.lean:29:  two : (cuts S a b).length = 2
PaidCaller.lean:30:  core : subtree T r = some C
PaidCaller.lean:31:  coreLabels : ∀ x, x ∈ leaves T → (x ∈ leaves C ↔ x ∉ leaves X ∧ x ≠ c)
PaidCaller.lean:32:  bC : b ∈ leaves C
PaidCaller.lean:33:  cC : c ∉ leaves C
PaidCaller.lean:34:  leafA : LeafAt T qa a
PaidCaller.lean:35:  leafB : LeafAt T ub b
PaidCaller.lean:36:  leafC : LeafAt T uc c
PaidCaller.lean:37:  frontier : incident T (leaves X) = [r,uc] ∨ incident T (leaves X) = [uc,r]
PaidCaller.lean:38:  tailR : r.dropLast ∈ minimalVertices (leaves X) T
PaidCaller.lean:39:  tailC : uc.dropLast ∈ minimalVertices (leaves X) T
PaidCaller.lean:40:  offR : r ∉ minimalVertices (leaves X) T
PaidCaller.lean:41:  offC : uc ∉ minimalVertices (leaves X) T
```

## source-PaidCurrentSource-CurrentReceipt.txt

```text
PaidCurrentSource.lean:8: structure CurrentReceipt where
PaidCurrentSource.lean:9:  value : Rule5PaidOrdinary.CurrentResult
PaidCurrentSource.lean:10:  prefixWork : Nat
PaidCurrentSource.lean:11:  forestDebit : Nat
PaidCurrentSource.lean:12:  ordinaryCalls : List Query
PaidCurrentSource.lean:13:  deriving Repr
```

## source-PaidCurrentSource-currentQueryMeter.txt

```text
PaidCurrentSource.lean:17: def currentQueryMeter (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) : CurrentReceipt :=
PaidCurrentSource.lean:18:  let p:=forestPretestMeter T ss
PaidCurrentSource.lean:19:  match p.value with
PaidCurrentSource.lean:20:  | .refused=>⟨.malformed,p.work+2,0,[]⟩
PaidCurrentSource.lean:21:  | .found F=>⟨.answered (if additionalCost ss F≤r then some F else none),p.work+F.length+ss.length+4,0,[]⟩
PaidCurrentSource.lean:22:  | .rejected=>if r≤1 then ⟨.answered none,p.work+3,0,[]⟩ else
PaidCurrentSource.lean:23:     ⟨.answered (GenericForest.solve cb T ss r),p.work+3,forestWork cb W T ss r,frontier cb T ss r⟩
```

## source-PaidDefs-Job.txt

```text
PaidDefs.lean:6: structure Job where
PaidDefs.lean:7:   T : Tree
PaidDefs.lean:8:   S : Tree
PaidDefs.lean:9:   budget : Nat
PaidDefs.lean:10:   deriving DecidableEq, Repr
```

## source-PaidForestCandidates-forestCandidatesMeter.txt

```text
PaidForestCandidates.lean:64: def forestCandidatesMeter (ss : List Tree) : Charged (List Forest) :=
PaidForestCandidates.lean:65:  let unchanged:=meterSourceLeaves ss;let one:=oneCutsMeter ss
PaidForestCandidates.lean:66:  ⟨unchanged.value::one.value,unchanged.work+one.work+2⟩
```

## source-PaidForestCandidates-oneCutsMeter.txt

```text
PaidForestCandidates.lean:11: def oneCutsMeter : List Tree→Charged (List Forest)
PaidForestCandidates.lean:12:  | []=>⟨[],1⟩
PaidForestCandidates.lean:13:  | s::ss=>
PaidForestCandidates.lean:14:    let es:=meterEdges s
PaidForestCandidates.lean:15:    let left:=meterMap (fun p=>let f:=meterForest s (some p);let u:=meterSourceLeaves ss
PaidForestCandidates.lean:16:     ⟨f.value++u.value,f.work+u.work+f.value.length+2⟩) es.value
PaidForestCandidates.lean:17:    let tail:=oneCutsMeter ss
PaidForestCandidates.lean:18:    let right:=meterMap (fun F=>let l:=meterLeaves s;⟨l.value::F,l.work+2⟩) tail.value
PaidForestCandidates.lean:19:    ⟨left.value++right.value,es.work+left.work+tail.work+right.work+left.value.length+3⟩
```

## source-PaidForestPretest-bestAdditionalMeter.txt

```text
PaidForestPretest.lean:10: def bestAdditionalMeter (ss : List Tree) (valid : Forest→Charged Bool) : List Forest→Charged (Option Forest)
PaidForestPretest.lean:11:  | []=>⟨none,1⟩
PaidForestPretest.lean:12:  | F::fs=>let a:=valid F;let r:=bestAdditionalMeter ss valid fs
PaidForestPretest.lean:13:            if a.value then
PaidForestPretest.lean:14:             match r.value with
PaidForestPretest.lean:15:             | none=>⟨some F,a.work+r.work+6⟩
PaidForestPretest.lean:16:             | some G=>⟨if ForestState.additionalCost ss F≤ForestState.additionalCost ss G then some F else some G,
PaidForestPretest.lean:17:                a.work+r.work+F.length+G.length+2*ss.length+8⟩
PaidForestPretest.lean:18:            else ⟨r.value,a.work+r.work+4⟩
```

## source-PaidForestPretest-forestPretestMeter.txt

```text
PaidForestPretest.lean:51: def forestPretestMeter (T : Option Tree) (ss : List Tree) : Charged ForestPretest01.Result :=
PaidForestPretest.lean:52:  let p:=meterProper T ss
PaidForestPretest.lean:53:  if p.value then
PaidForestPretest.lean:54:   let c:=forestCandidatesMeter ss;let b:=bestAdditionalMeter ss (meterAgrees T ss) c.value
PaidForestPretest.lean:55:   ⟨match b.value with | none=>.rejected | some F=>.found F,p.work+c.work+b.work+4⟩
PaidForestPretest.lean:56:  else ⟨.refused,p.work+2⟩
```

## source-PaidGuardSource-currentGuardMeter.txt

```text
PaidGuardSource.lean:45: def currentGuardMeter (T S : Tree) (c : Branch) : Charged Bool :=
PaidGuardSource.lean:46:  let n:=vertexNodupMeter c.originalCuts
PaidGuardSource.lean:47:  let a:=meterAll (fun q=>let s:=meterSubtree (current T S c) q;⟨!q.isEmpty&&s.value.isSome,s.work+3⟩) c.originalCuts
PaidGuardSource.lean:48:  let l:=meterLeaves (current T S c)
PaidGuardSource.lean:49:  let p:=meterPartition l.value c.partition
PaidGuardSource.lean:50:  let e:=meterPairwise (current T S c) c.partition
PaidGuardSource.lean:51:  let r:=arcPartitionMeter (current T S c) c.originalCuts
PaidGuardSource.lean:52:  let eq:=forestEqMeter c.partition r.value
PaidGuardSource.lean:53:  ⟨n.value&&a.value&&p.value&&e.value&&(c.partition.length==c.originalCuts.length+1)&&eq.value,
PaidGuardSource.lean:54:   n.work+a.work+l.work+p.work+e.work+r.work+eq.work+c.partition.length+2*c.originalCuts.length+18⟩
```

## source-PaidGuardSource-forestEqMeter_vertexNodupMeter.txt

```text
PaidGuardSource.lean:7: def vertexNodupMeter : List RMAF.Vertex→Charged Bool
PaidGuardSource.lean:8:  | []=>⟨true,1⟩
PaidGuardSource.lean:9:  | q::qs=>let c:=containsAddressMeter q qs;let r:=vertexNodupMeter qs
PaidGuardSource.lean:10:            ⟨!c.value&&r.value,c.work+r.work+3⟩

PaidGuardSource.lean:28: def forestEqMeter : List (List Nat)→List (List Nat)→Charged Bool
PaidGuardSource.lean:29:  | [],[]=>⟨true,1⟩ | [],_::_=>⟨false,1⟩ | _::_,[]=>⟨false,1⟩
PaidGuardSource.lean:30:  | B::P,C::Q=>let a:=natListEqMeter B C;let r:=forestEqMeter P Q;⟨a.value&&r.value,a.work+r.work+3⟩
```

## source-PaidGuardSource-guardedPlanMeter.txt

```text
PaidGuardSource.lean:61: def guardedPlanMeter {T S : Tree} (D : Case322PaidGuard.LiteralGeometry T S)
PaidGuardSource.lean:62:  (plan : Charged (List Branch)) : Charged (List Branch) :=
PaidGuardSource.lean:63:  let f:=meterFilter (currentGuardMeter T S) plan.value;⟨f.value,plan.work+f.work+2⟩
```

## source-PaidGuardSource-natListEqMeter.txt

```text
PaidGuardSource.lean:16: def natListEqMeter : List Nat→List Nat→Charged Bool
PaidGuardSource.lean:17:  | [],[]=>⟨true,1⟩ | [],_::_=>⟨false,1⟩ | _::_,[]=>⟨false,1⟩
PaidGuardSource.lean:18:  | x::xs,y::ys=>let r:=natListEqMeter xs ys;⟨(x==y)&&r.value,r.work+3⟩
```

## source-PaidOuterSource-PaidRoute.txt

```text
PaidOuterSource.lean:13: inductive PaidRoute where
PaidOuterSource.lean:14:  | empty
PaidOuterSource.lean:15:  | good : List Nat→List Nat→List Nat→PaidRoute
PaidOuterSource.lean:16:  | hard
PaidOuterSource.lean:17:  | bad : List Nat→List Nat→List Nat→(RMAF.Vertex×RMAF.Vertex)→PaidRoute
PaidOuterSource.lean:18:  deriving Repr
```

## source-PaidOuterSource-paidOuterMeter.txt

```text
PaidOuterSource.lean:20: def paidOuterMeter (T S : Tree) (c : CherryBranching.Candidate) (out : Result) : Charged PaidRoute :=
PaidOuterSource.lean:21:  match c.originalCuts with
PaidOuterSource.lean:22:  | [p,r]=>
PaidOuterSource.lean:23:   let parents:=hard2ParentsMeter S p r
PaidOuterSource.lean:24:   let A:=parents.value.1;let B:=parents.value.2.1;let C:=parents.value.2.2
PaidOuterSource.lean:25:   match out with
PaidOuterSource.lean:26:   | .pair o (.edge edge)=>
PaidOuterSource.lean:27:    let X:=first o A B C;let Y:=second o A B C;let Z:=third o A B C
PaidOuterSource.lean:28:    let x:=meterRestrictionAgrees S T X;let y:=meterRestrictionAgrees S T Y
PaidOuterSource.lean:29:    if x.value && y.value then
PaidOuterSource.lean:30:     ⟨.good X Y Z,parents.work+x.work+y.work+20⟩
PaidOuterSource.lean:31:    else
PaidOuterSource.lean:32:     let x2:=meterRestrictionAgrees S T X;let y2:=meterRestrictionAgrees S T Y
PaidOuterSource.lean:33:     ⟨if x2.value || y2.value then .hard else .bad X Y Z edge,
PaidOuterSource.lean:34:      parents.work+x.work+y.work+x2.work+y2.work+28⟩
PaidOuterSource.lean:35:   | _=>⟨.hard,parents.work+12⟩
PaidOuterSource.lean:36:  | _=>⟨.empty,8⟩
```

## source-PaidOutputDefs-Kind.txt

```text
PaidOutputDefs.lean:7: inductive Kind where
PaidOutputDefs.lean:8:  | clique : RMAF.Vertex → Kind
PaidOutputDefs.lean:9:  | four : RMAF.Vertex → RMAF.Vertex → Kind
PaidOutputDefs.lean:10:  | diagonal : RMAF.Vertex → RMAF.Vertex → Kind
PaidOutputDefs.lean:11:  | vertex : RMAF.Vertex → Kind
PaidOutputDefs.lean:12:  | side : List Nat → Kind
PaidOutputDefs.lean:13:  deriving DecidableEq,Repr
```

## source-PaidParsing-fmMeter_rowAtMeter.txt

```text
PaidParsing.lean:57: def fmMeter {α β : Type} (f : α→Measured (List β)) : List α→Measured (List β)
PaidParsing.lean:58:  | []=>⟨[],1⟩
PaidParsing.lean:59:  | x::xs=>let a:=f x;let r:=fmMeter f xs;⟨a.value++r.value,a.work+r.work+a.value.length+3⟩

PaidParsing.lean:87: def rowAtMeter (S : Tree) (w : RMAF.Vertex) (a b c : Nat) : Measured (List BottomData) :=
PaidParsing.lean:88:  fmMeter (fun sa=>fmMeter (fun sc=>fmMeter (fun sb=>pairRowsMeter S w sa sc sb a b c)
PaidParsing.lean:89:   [false,true]) [false,true]) [false,true]
```

## source-PaidParsing-leafEqMeter.txt

```text
PaidParsing.lean:7: def leafEqMeter (T : Tree) (x : Nat) : Measured Bool := ⟨decide (T=.leaf x),3⟩
```

## source-PaidParsing-pairRowsMeter.txt

```text
PaidParsing.lean:83: def pairRowsMeter (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) : Measured (List BottomData) :=
PaidParsing.lean:84:  fmMeter (fun xy=>let p:=parseBottomMeter S w sa sc sb xy.1 xy.2 c
PaidParsing.lean:85:   ⟨match p.value with | none=>[] | some X=>[(⟨w,sa,sc,sb,xy.1,xy.2,X⟩:BottomData)],p.work+2⟩) [(a,b),(b,a)]
```

## source-PaidParsing-parseBottomMeter.txt

```text
PaidParsing.lean:9: def parseBottomMeter (S : Tree) (w : RMAF.Vertex) (sa sc sb : Bool) (a b c : Nat) : Measured (Option Tree) :=
PaidParsing.lean:10:  let z:=subtreeMeter S w
PaidParsing.lean:11:  let finish : Measured (Option Tree):=
PaidParsing.lean:12:   match z.value with
PaidParsing.lean:13:   | none=>⟨none,1⟩
PaidParsing.lean:14:   | some Z=>
PaidParsing.lean:15:     match unorient sb Z with
PaidParsing.lean:16:     | none=>⟨none,2⟩
PaidParsing.lean:17:     | some (V,B)=>
PaidParsing.lean:18:       match unorient sc V with
PaidParsing.lean:19:       | none=>⟨none,4⟩
PaidParsing.lean:20:       | some (A,C)=>
PaidParsing.lean:21:         match unorient sa A with
PaidParsing.lean:22:         | none=>⟨none,6⟩
PaidParsing.lean:23:         | some (L,X)=>
PaidParsing.lean:24:           let eb:=leafEqMeter B b;let ec:=leafEqMeter C c;let ea:=leafEqMeter L a
PaidParsing.lean:25:           ⟨if eb.value && ec.value && ea.value then some X else none,eb.work+ec.work+ea.work+9⟩
PaidParsing.lean:26:  ⟨finish.value,z.work+finish.work+1⟩
```

## source-PaidParsing-rowsMeter.txt

```text
PaidParsing.lean:91: def rowsMeter (S : Tree) (a b c : Nat) : Measured (List BottomData) :=
PaidParsing.lean:92:  let v:=verticesMeter S;let r:=fmMeter (fun w=>rowAtMeter S w a b c) v.value
PaidParsing.lean:93:  ⟨r.value,v.work+r.work+1⟩
```

## source-PaidPlanSource-bBranchMeter_hardBranchMeter_sideAtMeter_sideEdgesMeter_targetBranchMeter.txt

```text
PaidPlanSource.lean:9: def sideAtMeter (T : Tree) (b c : Nat) (q : RMAF.Vertex) : Charged Bool :=
PaidPlanSource.lean:10:  let d:=dropLastMeter q;let x:=meterSubtreeLabels T d.value;let bx:=meterContains b x.value
PaidPlanSource.lean:11:  let e:=dropLastMeter q;let y:=meterSubtreeLabels T e.value;let cy:=meterContains c y.value
PaidPlanSource.lean:12:  ⟨bx.value && !cy.value,d.work+x.work+bx.work+e.work+y.work+cy.work+3⟩

PaidPlanSource.lean:17: def sideEdgesMeter (T : Tree) (b c : Nat) : Charged (List RMAF.Vertex) :=
PaidPlanSource.lean:18:  let k:=cutsMeter T b c;let f:=meterFilter (sideAtMeter T b c) k.value
PaidPlanSource.lean:19:  ⟨f.value,k.work+f.work+2⟩

PaidPlanSource.lean:49: def hardBranchMeter (S : Tree) (a b : Nat) : Charged Branch :=
PaidPlanSource.lean:50:  let k:=cutsMeter S a b;let p:=partitionMeter S a b
PaidPlanSource.lean:51:  ⟨⟨.source,k.value,p.value⟩,k.work+p.work+4⟩

PaidPlanSource.lean:52: def bBranchMeter (S : Tree) (b : Nat) (qb : RMAF.Vertex) : Charged Branch :=
PaidPlanSource.lean:53:  let p:=singletonPartitionMeter S b;⟨⟨.source,[qb],p.value⟩,p.work+4⟩

PaidPlanSource.lean:54: def targetBranchMeter (T : Tree) (qs : List RMAF.Vertex) : Charged Branch :=
PaidPlanSource.lean:55:  let p:=arcPartitionMeter T qs;⟨⟨.target,qs,p.value⟩,p.work+3⟩
```

## source-PaidPlanSource-cSideMeter_lcaMeter_typeIIMeter_typeIMeter_withoutAMeter.txt

```text
PaidPlanSource.lean:23: def cSideMeter (T : Tree) (b c : Nat) : Charged (List RMAF.Vertex) :=
PaidPlanSource.lean:24:  let k:=cutsMeter T b c;let f:=meterFilter (sideAtMeter T c b) k.value
PaidPlanSource.lean:25:  ⟨f.value,k.work+f.work+2⟩

PaidPlanSource.lean:29: def withoutAMeter (T : Tree) (a b c : Nat) : Charged (List RMAF.Vertex) :=
PaidPlanSource.lean:30:  let s:=sideEdgesMeter T b c
PaidPlanSource.lean:31:  let f:=meterFilter (fun q=>let x:=meterSubtreeLabels T q;let z:=meterContains a x.value;⟨!z.value,x.work+z.work+1⟩) s.value
PaidPlanSource.lean:32:  ⟨f.value,s.work+f.work+2⟩

PaidPlanSource.lean:36: def lcaMeter : RMAF.Vertex→RMAF.Vertex→Charged RMAF.Vertex
PaidPlanSource.lean:37:  | [],_=>⟨[],1⟩ | _::_,[]=>⟨[],1⟩
PaidPlanSource.lean:38:  | x::xs,y::ys=>if x=y then let r:=lcaMeter xs ys;⟨x::r.value,r.work+3⟩ else ⟨[],2⟩

PaidPlanSource.lean:60: def typeIMeter (T S : Tree) (a b : Nat) (qa qb q r : RMAF.Vertex) : Charged (List Branch) :=
PaidPlanSource.lean:61:  let h:=hardBranchMeter S a b;let s:=bBranchMeter S b qb
PaidPlanSource.lean:62:  let l:=targetBranchMeter T [qa,q];let u:=targetBranchMeter T [qa,r]
PaidPlanSource.lean:63:  ⟨[h.value,s.value,l.value,u.value],h.work+s.work+l.work+u.work+5⟩

PaidPlanSource.lean:64: def typeIIMeter (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) : Charged (List Branch) :=
PaidPlanSource.lean:65:  let h:=hardBranchMeter S a b;let s:=bBranchMeter S b qb;let l:=targetBranchMeter T (qa::qs)
PaidPlanSource.lean:66:  ⟨[h.value,s.value,l.value],h.work+s.work+l.work+4⟩
```

## source-PaidPlanSource-literalPlanMeter.txt

```text
PaidPlanSource.lean:89: def literalPlanMeter {T S : Tree} (D : LiteralGeometry T S) : Charged (List Branch) :=
PaidPlanSource.lean:90:  let p:=rawPlanMeter T S D.a D.b D.c D.qa (bArc D.w D.sb) D.ub D.uc
PaidPlanSource.lean:91:  ⟨p.value,p.work+D.w.length+2⟩
```

## source-PaidPlanSource-rawPlanMeter.txt

```text
PaidPlanSource.lean:72: def rawPlanMeter (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) : Charged (List Branch) :=
PaidPlanSource.lean:73:  let es:=cSideMeter T b c
PaidPlanSource.lean:74:  match es.value with
PaidPlanSource.lean:75:  | q::r::_=>let p:=typeIMeter T S a b qa qb q r;⟨p.value,es.work+p.work+3⟩
PaidPlanSource.lean:76:  | _=>let bs:=withoutAMeter T a b c
PaidPlanSource.lean:77:       match bs.value with
PaidPlanSource.lean:78:       | []=>let l:=lcaMeter ub uc;let p:=typeIIMeter T S a b qa qb [l.value];⟨p.value,es.work+bs.work+l.work+p.work+5⟩
PaidPlanSource.lean:79:       | qs=>let p:=typeIIMeter T S a b qa qb qs;⟨p.value,es.work+bs.work+p.work+3⟩
```

## source-PaidRequests-PaidRequest.txt

```text
PaidRequests.lean:9: structure PaidRequest where
PaidRequests.lean:10:  branch : Branch
PaidRequests.lean:11:  target : Tree
PaidRequests.lean:12:  sources : List Tree
PaidRequests.lean:13:  residual : Nat
PaidRequests.lean:14:  deriving DecidableEq, Repr
```

## source-PaidRequests-opposite.txt

```text
PaidRequests.lean:7: def opposite (T S : Tree) (c : Branch) : Tree := if c.role=.source then T else S
```

## source-PaidRequestsSource-PaidExecutionReceipt.txt

```text
PaidRequestsSource.lean:41: structure PaidExecutionReceipt (α : Type) where
PaidRequestsSource.lean:42:  value : α
PaidRequestsSource.lean:43:  prefixWork : Nat
PaidRequestsSource.lean:44:  forestDebit : Nat
PaidRequestsSource.lean:45:  ordinaryCalls : List GenericForest.FrontierWork.Query
PaidRequestsSource.lean:46:  deriving Repr
```

## source-PaidRequestsSource-answerListMeter_requestsMeter.txt

```text
PaidRequestsSource.lean:33: def requestsMeter {T S : Tree} (D : LiteralGeometry T S) (q : Nat) : Charged (List PaidRequest) :=
PaidRequestsSource.lean:34:  let p:=literalPlanMeter D;let g:=guardedPlanMeter D p;let r:=requestListMeter T S q g.value
PaidRequestsSource.lean:35:  ⟨r.value,g.work+r.work+2⟩

PaidRequestsSource.lean:55: def answerListMeter (cb : Ordinary) (W : OrdinaryWork) : List PaidRequest→PaidExecutionReceipt (List Forest)
PaidRequestsSource.lean:56:  | []=>⟨[],1,0,[]⟩
PaidRequestsSource.lean:57:  | j::js=>let a:=requestAnswerMeter cb W j;let r:=answerListMeter cb W js
PaidRequestsSource.lean:58:            ⟨match a.value with | none=>r.value | some F=>F::r.value,
PaidRequestsSource.lean:59:              a.prefixWork+r.prefixWork+3,a.forestDebit+r.forestDebit,a.ordinaryCalls++r.ordinaryCalls⟩
```

## source-PaidRequestsSource-answersMeter.txt

```text
PaidRequestsSource.lean:68: def answersMeter (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : PaidExecutionReceipt (List Forest) :=
PaidRequestsSource.lean:69:  let js:=requestsMeter R.geometry q;let a:=answerListMeter cb W js.value
PaidRequestsSource.lean:70:  ⟨a.value,js.work+a.prefixWork+2,a.forestDebit,a.ordinaryCalls⟩
```

## source-PaidRequestsSource-requestAnswerMeter_requestListMeter.txt

```text
PaidRequestsSource.lean:19: def requestListMeter (T S : Tree) (q : Nat) : List Branch→Charged (List PaidRequest)
PaidRequestsSource.lean:20:  | []=>⟨[],1⟩
PaidRequestsSource.lean:21:  | c::cs=>let a:=requestForMeter T S q c;let r:=requestListMeter T S q cs
PaidRequestsSource.lean:22:            ⟨match a.value with | none=>r.value | some j=>j::r.value,a.work+r.work+3⟩

PaidRequestsSource.lean:48: def requestAnswerMeter (cb : Ordinary) (W : OrdinaryWork) (j : PaidRequest) : PaidExecutionReceipt (Option Forest) :=
PaidRequestsSource.lean:49:  let a:=currentQueryMeter cb W (some j.target) j.sources j.residual
PaidRequestsSource.lean:50:  ⟨a.value.answer?,a.prefixWork+1,a.forestDebit,a.ordinaryCalls⟩
```

## source-PaidRequestsSource-requestForMeter.txt

```text
PaidRequestsSource.lean:7: def requestForMeter (T S : Tree) (q : Nat) (c : Branch) : Charged (Option PaidRequest) :=
PaidRequestsSource.lean:8:  if c.originalCuts.length≤q then
PaidRequestsSource.lean:9:   let s:=sourceForestMeter (current T S c) c.partition
PaidRequestsSource.lean:10:   ⟨some ⟨c,opposite T S c,s.value,q-c.originalCuts.length⟩,s.work+2*c.originalCuts.length+7⟩
PaidRequestsSource.lean:11:  else ⟨none,c.originalCuts.length+2⟩
```

## source-PaidSelectedBinding-paidSelectedMeter.txt

```text
PaidSelectedBinding.lean:7: def paidSelectedMeter (classFee : CheckRequest→Nat) (literalFee : LiteralCall→Nat)
PaidSelectedBinding.lean:8:  (T S : Tree) (a b : Nat) : Measured (Option (SelectedPaid T S)) :=
PaidSelectedBinding.lean:9:  let cls:=finalMeter classFee T S a b
PaidSelectedBinding.lean:10:  match cls.value with
PaidSelectedBinding.lean:11:  | some (.remaining d (.second u v))=>
PaidSelectedBinding.lean:12:    let r:=secondBuilderMeter literalFee T S a b d u v
PaidSelectedBinding.lean:13:    ⟨r.value.map (SelectedPaid.mk d u v),cls.work+r.work+2⟩
PaidSelectedBinding.lean:14:  | _=>⟨none,cls.work+1⟩
```

## source-PaintCost-meterBest.txt

```text
PaintCost.lean:42: def meterBest {α : Type} (cost : α → Charged Nat) : List α → Charged (Option α)
PaintCost.lean:43:  | [] => ⟨none,4⟩
PaintCost.lean:44:  | a::as =>
PaintCost.lean:45:   let r := meterBest cost as
PaintCost.lean:46:   match r.value with
PaintCost.lean:47:   | none => ⟨some a,r.work+8⟩
PaintCost.lean:48:   | some b =>
PaintCost.lean:49:    let ca := cost a
PaintCost.lean:50:    let cb := cost b
PaintCost.lean:51:    ⟨if ca.value≤cb.value then some a else some b,r.work+ca.work+cb.work+12⟩
```

## source-PaintCost-meterChanges_meterChoose.txt

```text
PaintCost.lean:15: def meterChanges : Paint → Charged Nat
PaintCost.lean:16:  | .leaf _ _ => ⟨0,4⟩
PaintCost.lean:17:  | .node c l r =>
PaintCost.lean:18:   let a := meterChanges l
PaintCost.lean:19:   let b := meterChanges r
PaintCost.lean:20:   ⟨a.value+delta c (root l)+b.value+delta c (root r),a.work+b.work+16⟩

PaintCost.lean:74: def meterChoose (cost : Paint → Charged Nat) (xs : List Paint) : Charged Paint :=
PaintCost.lean:75:  let m := meterBest cost xs
PaintCost.lean:76:  ⟨m.value.getD (.leaf 0 0),m.work+4⟩
```

## source-PaintCost-meterEdgeCost.txt

```text
PaintCost.lean:30: def meterEdgeCost (c : Nat) (p : Paint) : Charged Nat :=
PaintCost.lean:31:  let m := meterChanges p
PaintCost.lean:32:  ⟨m.value+delta c (root p),m.work+8⟩
```

## source-PendantAddressScans-containsAddressMeter_dropLastMeter.txt

```text
PendantAddressScans.lean:25: def containsAddressMeter (p : RMAF.Vertex) : List RMAF.Vertex→Measured Bool
PendantAddressScans.lean:26:  | []=>⟨false,1⟩
PendantAddressScans.lean:27:  | q::qs=>let c:=eqAddressMeter p q
PendantAddressScans.lean:28:            if c.value then ⟨true,c.work+1⟩ else let r:=containsAddressMeter p qs;⟨r.value,c.work+r.work+1⟩

PendantAddressScans.lean:48: def dropLastMeter : RMAF.Vertex→Measured RMAF.Vertex
PendantAddressScans.lean:49:  | []=>⟨[],1⟩
PendantAddressScans.lean:50:  | [_]=>⟨[],1⟩
PendantAddressScans.lean:51:  | x::y::xs=>let r:=dropLastMeter (y::xs);⟨x::r.value,r.work+2⟩
```

## source-PendantAddressScans-eqAddressMeter.txt

```text
PendantAddressScans.lean:5: def eqAddressMeter : RMAF.Vertex→RMAF.Vertex→Measured Bool
PendantAddressScans.lean:6:  | [],[]=>⟨true,1⟩
PendantAddressScans.lean:7:  | [],_::_=>⟨false,1⟩
PendantAddressScans.lean:8:  | _::_,[]=>⟨false,1⟩
PendantAddressScans.lean:9:  | x::xs,y::ys=>if x==y then let r:=eqAddressMeter xs ys;⟨r.value,r.work+2⟩ else ⟨false,2⟩
```

## source-PendantCandidates-candidateRowsMeter.txt

```text
PendantCandidates.lean:5: def candidateRowsMeter (S : Tree) : List CherryRow→Measured (List Candidate)
PendantCandidates.lean:6:  | []=>⟨[],1⟩
PendantCandidates.lean:7:  | (p,a,b)::cs=>let e:=cutsMeter S a b;let r:=candidateRowsMeter S cs
PendantCandidates.lean:8:                 ⟨⟨p,a,b,e.value⟩::r.value,e.work+r.work+6⟩
```

## source-PendantCandidates-candidatesMeter_earlierAllMeter.txt

```text
PendantCandidates.lean:26: def candidatesMeter (T S : Tree) : Measured (List Candidate) :=
PendantCandidates.lean:27:  let c:=cherriesMeter T;let r:=candidateRowsMeter S c.value
PendantCandidates.lean:28:  ⟨r.value,c.work+r.work+1⟩

PendantCandidates.lean:60: def earlierAllMeter : List Candidate→Measured Bool
PendantCandidates.lean:61:  | []=>⟨true,1⟩
PendantCandidates.lean:62:  | c::cs=>if c.originalCuts.length==2 then
PendantCandidates.lean:63:              let r:=earlierAllMeter cs;⟨r.value,c.originalCuts.length+r.work+2⟩
PendantCandidates.lean:64:            else ⟨false,c.originalCuts.length+2⟩
```

## source-PendantCandidates-earlierMeter.txt

```text
PendantCandidates.lean:83: def earlierMeter (T S : Tree) : Measured Bool :=
PendantCandidates.lean:84:  let c:=candidatesMeter T S;let a:=earlierAllMeter c.value
PendantCandidates.lean:85:  ⟨a.value,c.work+a.work+1⟩
```

## source-PendantCutWork-cutFilterMeter.txt

```text
PendantCutWork.lean:41: def cutFilterMeter (S : Tree) (a b : Nat) : List RMAF.Vertex→Measured (List RMAF.Vertex)
PendantCutWork.lean:42:  | []=>⟨[],1⟩
PendantCutWork.lean:43:  | v::vs=>let c:=cutGuardMeter S a b v;let r:=cutFilterMeter S a b vs
PendantCutWork.lean:44:            ⟨if c.value then v::r.value else r.value,c.work+r.work+2⟩
```

## source-PendantCutWork-cutGuardMeter.txt

```text
PendantCutWork.lean:5: def cutGuardMeter (S : Tree) (a b : Nat) (v : RMAF.Vertex) : Measured Bool :=
PendantCutWork.lean:6:  if v.isEmpty then ⟨false,1⟩ else
PendantCutWork.lean:7:  let p:=dropLastMeter v;let m:=minimalMeter [a,b] S
PendantCutWork.lean:8:  let c:=containsAddressMeter p.value m.value
PendantCutWork.lean:9:  if c.value then let m2:=minimalMeter [a,b] S;let d:=containsAddressMeter v m2.value
PendantCutWork.lean:10:   ⟨!d.value,p.work+m.work+c.work+m2.work+d.work+3⟩
PendantCutWork.lean:11:  else ⟨false,p.work+m.work+c.work+2⟩
```

## source-PendantCutWork-cutsMeter.txt

```text
PendantCutWork.lean:64: def cutsMeter (S : Tree) (a b : Nat) : Measured (List RMAF.Vertex) :=
PendantCutWork.lean:65:  let v:=verticesMeter S;let f:=cutFilterMeter S a b v.value
PendantCutWork.lean:66:  ⟨f.value,v.work+f.work+1⟩
```

## source-PendantMinimal-minimalMeter.txt

```text
PendantMinimal.lean:5: def minimalMeter (D : List Nat) : Tree→Measured (List RMAF.Vertex)
PendantMinimal.lean:6:  | .leaf x=>let c:=containsMeter x D;⟨if c.value then [[]] else [],c.work+2⟩
PendantMinimal.lean:7:  | .node l r=>let a:=spanMeter D l;let b:=spanMeter D r
PendantMinimal.lean:8:                if a.value.isEmpty then
PendantMinimal.lean:9:                 let m:=minimalMeter D r
PendantMinimal.lean:10:                 ⟨prependSide true m.value,a.work+b.work+m.work+4*m.value.length+3⟩
PendantMinimal.lean:11:                else if b.value.isEmpty then
PendantMinimal.lean:12:                 let m:=minimalMeter D l
PendantMinimal.lean:13:                 ⟨prependSide false m.value,a.work+b.work+m.work+4*m.value.length+3⟩
PendantMinimal.lean:14:                else ⟨[]::(prependSide false a.value++prependSide true b.value),
PendantMinimal.lean:15:                  a.work+b.work+6*a.value.length+5*b.value.length+3⟩
```

## source-PendantPartitionWork-coreFilterMeter.txt

```text
PendantPartitionWork.lean:55: def coreFilterMeter (S : Tree) (a b : Nat) : List Nat→Measured (List Nat)
PendantPartitionWork.lean:56:  | []=>⟨[],1⟩
PendantPartitionWork.lean:57:  | x::xs=>let p:=pendantPayloadMeter S a b;let c:=containsMeter x p.value
PendantPartitionWork.lean:58:            let r:=coreFilterMeter S a b xs
PendantPartitionWork.lean:59:            ⟨if !c.value then x::r.value else r.value,p.work+c.work+r.work+2⟩
```

## source-PendantPartitionWork-coreMeter.txt

```text
PendantPartitionWork.lean:78: def coreMeter (S : Tree) (a b : Nat) : Measured (List Nat) :=
PendantPartitionWork.lean:79:  let l:=leavesMeter S;let f:=coreFilterMeter S a b l.value
PendantPartitionWork.lean:80:  ⟨f.value,l.work+f.work+1⟩
```

## source-PendantPartitionWork-partitionMeter.txt

```text
PendantPartitionWork.lean:98: def partitionMeter (S : Tree) (a b : Nat) : Measured (List (List Nat)) :=
PendantPartitionWork.lean:99:  let e:=cutsMeter S a b;let bs:=blocksMeter S e.value;let c:=coreMeter S a b
PendantPartitionWork.lean:100:  ⟨bs.value++[c.value],e.work+bs.work+c.work+bs.value.length+3⟩
```

## source-PendantPartitionWork-pendantPayloadMeter.txt

```text
PendantPartitionWork.lean:8: def pendantPayloadMeter (S : Tree) (a b : Nat) : Measured (List Nat) :=
PendantPartitionWork.lean:9:  let e:=cutsMeter S a b;let bs:=blocksMeter S e.value;let f:=flattenMeter bs.value
PendantPartitionWork.lean:10:  ⟨f.value,e.work+bs.work+f.work+2⟩
```

## source-PendantSpan-spanMeter.txt

```text
PendantSpan.lean:5: def spanMeter (D : List Nat) : Tree→Measured (List RMAF.Vertex)
PendantSpan.lean:6:  | .leaf x=>let c:=containsMeter x D
PendantSpan.lean:7:             ⟨if c.value then [[]] else [],c.work+2⟩
PendantSpan.lean:8:  | .node l r=>let a:=spanMeter D l;let b:=spanMeter D r
PendantSpan.lean:9:                if a.value.isEmpty && b.value.isEmpty then ⟨[],a.work+b.work+2⟩
PendantSpan.lean:10:                else ⟨[]::(prependSide false a.value++prependSide true b.value),
PendantSpan.lean:11:                  a.work+b.work+6*a.value.length+5*b.value.length+3⟩
```

## source-PendantSubtrees-blocksMeter.txt

```text
PendantSubtrees.lean:42: def blocksMeter (T : Tree) : List RMAF.Vertex→Measured (List (List Nat))
PendantSubtrees.lean:43:  | []=>⟨[],1⟩
PendantSubtrees.lean:44:  | p::ps=>let b:=subtreeLabelsMeter T p;let r:=blocksMeter T ps
PendantSubtrees.lean:45:            ⟨b.value::r.value,b.work+r.work+1⟩
```

## source-PendantSubtrees-flattenMeter.txt

```text
PendantSubtrees.lean:82: def flattenMeter : List (List Nat)→Measured (List Nat)
PendantSubtrees.lean:83:  | []=>⟨[],1⟩
PendantSubtrees.lean:84:  | B::bs=>let r:=flattenMeter bs;⟨B++r.value,r.work+B.length+1⟩
```

## source-PendantSubtrees-subtreeLabelsMeter.txt

```text
PendantSubtrees.lean:5: def subtreeLabelsMeter : Tree→RMAF.Vertex→Measured (List Nat)
PendantSubtrees.lean:6:  | T,[]=>let l:=leavesMeter T;⟨l.value,l.work+1⟩
PendantSubtrees.lean:7:  | .leaf _,_::_=>⟨[],1⟩
PendantSubtrees.lean:8:  | .node l r,s::p=>let m:=subtreeLabelsMeter (if s then r else l) p;⟨m.value,m.work+2⟩
```

## source-PendantVertices-verticesMeter.txt

```text
PendantVertices.lean:5: def verticesMeter : Tree→Measured (List RMAF.Vertex)
PendantVertices.lean:6:  | .leaf _=>⟨[[]],2⟩
PendantVertices.lean:7:  | .node l r=>let a:=verticesMeter l;let b:=verticesMeter r
PendantVertices.lean:8:                ⟨[]::(prependSide false a.value++prependSide true b.value),
PendantVertices.lean:9:                a.work+b.work+5*a.value.length+4*b.value.length+3⟩
```

## source-Planner-Entry.txt

```text
Planner.lean:15: structure Entry where
Planner.lean:16:   output : Output
Planner.lean:17:   mode : Mode
Planner.lean:18:   budget : Nat
```

## source-Planner-Mode_Mode.extra.txt

```text
Planner.lean:6: inductive Mode where
Planner.lean:7:   | ordinary
Planner.lean:8:   | full
Planner.lean:9:   | retained (parent residual completed : List Nat) (knownOne : Forest)

Planner.lean:11: def Mode.extra : Mode → Nat
Planner.lean:12:   | .retained _ _ _ _ => 1
Planner.lean:13:   | _ => 0
```

## source-PoolClassificationSelector-Candidate_Child_Priority.txt

```text
PoolClassificationSelector.lean:63: structure Candidate where
PoolClassificationSelector.lean:64:  parent : RMAF.Vertex
PoolClassificationSelector.lean:65:  a : Nat
PoolClassificationSelector.lean:66:  b : Nat
PoolClassificationSelector.lean:67:  originalCuts : List RMAF.Vertex
PoolClassificationSelector.lean:68:  deriving Repr, DecidableEq

PoolClassificationSelector.lean:73: inductive Priority where
PoolClassificationSelector.lean:74:  | common | one | high | hard2
PoolClassificationSelector.lean:75:  deriving Repr, DecidableEq

PoolClassificationSelector.lean:97: structure Child where
PoolClassificationSelector.lean:98:  partition : List (List Nat)
PoolClassificationSelector.lean:99:  sourceForest : List Tree
PoolClassificationSelector.lean:100:  paid : Nat
PoolClassificationSelector.lean:101:  deriving Repr, DecidableEq
```

## source-PoolClassificationSelector-remaining.txt

```text
PoolClassificationSelector.lean:120: def remaining (budget : Nat) (c : Child) : Option Nat :=
PoolClassificationSelector.lean:121:  if c.paid ≤ budget then some (budget-c.paid) else none
```

## source-PrefixChildrenWork-excludeOneMeter.txt

```text
PrefixChildrenWork.lean:7: def excludeOneMeter (x : Nat) : List Nat→Measured (List Nat)
PrefixChildrenWork.lean:8:  | []=>⟨[],1⟩
PrefixChildrenWork.lean:9:  | z::zs=>let r:=excludeOneMeter x zs;⟨if z != x then z::r.value else r.value,r.work+3⟩
```

## source-PrefixChildrenWork-excludeTwoMeter.txt

```text
PrefixChildrenWork.lean:10: def excludeTwoMeter (x y : Nat) : List Nat→Measured (List Nat)
PrefixChildrenWork.lean:11:  | []=>⟨[],1⟩
PrefixChildrenWork.lean:12:  | z::zs=>let r:=excludeTwoMeter x y zs;⟨if z != x && z != y then z::r.value else r.value,r.work+4⟩
```

## source-PrefixChildrenWork-fiveChildrenMeter.txt

```text
PrefixChildrenWork.lean:135: def fiveChildrenMeter (S : Tree) (a b p q : Nat) : Measured (List Child) :=
PrefixChildrenWork.lean:136:  let c:=pendantChildMeter S a b;let pa:=pairChildMeter S p a;let pb:=pairChildMeter S p b
PrefixChildrenWork.lean:137:  let qa:=pairChildMeter S q a;let qb:=pairChildMeter S q b
PrefixChildrenWork.lean:138:  ⟨[c.value,pa.value,pb.value,qa.value,qb.value],c.work+pa.work+pb.work+qa.work+qb.work+6⟩
```

## source-PrefixChildrenWork-localChildrenMeter.txt

```text
PrefixChildrenWork.lean:156: def localChildrenMeter (S : Tree) (a b : Nat) : LocalSelection→Measured (List Child)
PrefixChildrenWork.lean:157:  | .large _=>let c:=pendantChildMeter S a b;⟨[c.value],c.work+2⟩
PrefixChildrenWork.lean:158:  | .two c=>fiveChildrenMeter S a b c.p c.q
PrefixChildrenWork.lean:159:  | .outside c=>fiveChildrenMeter S a b c.p c.q
PrefixChildrenWork.lean:160:  | .remaining=>⟨[],1⟩
```

## source-PrefixChildrenWork-pairChildMeter.txt

```text
PrefixChildrenWork.lean:97: def pairChildMeter (S : Tree) (x y : Nat) : Measured Child :=
PrefixChildrenWork.lean:98:  let p:=pairPartitionMeter S x y;let c:=makeChildMeter S p.value 2
PrefixChildrenWork.lean:99:  ⟨c.value,p.work+c.work+1⟩
```

## source-PrefixChildrenWork-pairPartitionMeter.txt

```text
PrefixChildrenWork.lean:36: def pairPartitionMeter (S : Tree) (x y : Nat) : Measured (List (List Nat)) :=
PrefixChildrenWork.lean:37:  let l:=leavesMeter S;let f:=excludeTwoMeter x y l.value
PrefixChildrenWork.lean:38:  ⟨[[x],[y],f.value],l.work+f.work+7⟩
```

## source-PrefixChildrenWork-singletonChildMeter.txt

```text
PrefixChildrenWork.lean:94: def singletonChildMeter (S : Tree) (x : Nat) : Measured Child :=
PrefixChildrenWork.lean:95:  let p:=singletonPartitionMeter S x;let c:=makeChildMeter S p.value 1
PrefixChildrenWork.lean:96:  ⟨c.value,p.work+c.work+1⟩
```

## source-PrefixChildrenWork-singletonPartitionMeter.txt

```text
PrefixChildrenWork.lean:33: def singletonPartitionMeter (S : Tree) (x : Nat) : Measured (List (List Nat)) :=
PrefixChildrenWork.lean:34:  let l:=leavesMeter S;let f:=excludeOneMeter x l.value
PrefixChildrenWork.lean:35:  ⟨[[x],f.value],l.work+f.work+5⟩
```

## source-PrefixClassifierWork-largeAtMeter_optionsHeadMeter_sizeTwoAtMeter.txt

```text
PrefixClassifierWork.lean:5: def largeAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) : CheckReceipt (Option RMAF.Vertex) :=
PrefixClassifierWork.lean:6:  let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
PrefixClassifierWork.lean:7:  if c.value then let m:=subtreeLabelsMeter S e
PrefixClassifierWork.lean:8:   ⟨if 3≤m.value.length then some e else none,l.work+c.work+m.work+m.value.length+4,c.calls⟩
PrefixClassifierWork.lean:9:  else ⟨none,l.work+c.work+2,c.calls⟩

PrefixClassifierWork.lean:41: def optionsHeadMeter {α β : Type} (cs : Measured (List α)) (f : α→CheckReceipt (Option β)) : CheckReceipt (Option β) :=
PrefixClassifierWork.lean:42:  let r:=optionsMeter f cs.value;⟨r.value.head?,cs.work+r.work+2,r.calls⟩

PrefixClassifierWork.lean:81: def sizeTwoAtMeter (fee : CheckRequest→Nat) (T S : Tree) (e : RMAF.Vertex) : CheckReceipt (Option SizeTwoSelection) :=
PrefixClassifierWork.lean:82:  let l:=subtreeLabelsMeter S e;let c:=checkMeter fee (.restriction T S l.value)
PrefixClassifierWork.lean:83:  if c.value then let t:=subtreeMeter S e
PrefixClassifierWork.lean:84:   ⟨match t.value with | some (.node (.leaf p) (.leaf q))=>some ⟨e,p,q⟩ | _=>none,l.work+c.work+t.work+5,c.calls⟩
PrefixClassifierWork.lean:85:  else ⟨none,l.work+c.work+2,c.calls⟩
```

## source-PrefixClassifierWork-selectLargeMeter_selectSizeTwoMeter.txt

```text
PrefixClassifierWork.lean:55: def selectLargeMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option RMAF.Vertex) :=
PrefixClassifierWork.lean:56:  optionsHeadMeter (cutsMeter S a b) (largeAtMeter fee T S)

PrefixClassifierWork.lean:108: def selectSizeTwoMeter (fee : CheckRequest→Nat) (T S : Tree) (a b : Nat) : CheckReceipt (Option SizeTwoSelection) :=
PrefixClassifierWork.lean:109:  optionsHeadMeter (cutsMeter S a b) (sizeTwoAtMeter fee T S)
```

## source-PrefixLeaves-leavesMeter.txt

```text
PrefixLeaves.lean:5: def leavesMeter : Tree→Measured (List Nat)
PrefixLeaves.lean:6:  | .leaf x=>⟨[x],1⟩
PrefixLeaves.lean:7:  | .node l r=>let a:=leavesMeter l;let b:=leavesMeter r
PrefixLeaves.lean:8:                ⟨a.value++b.value,a.work+b.work+a.value.length+2⟩
```

## source-PrefixScans-Measured.txt

```text
PrefixScans.lean:4: structure Measured (α : Type) where
PrefixScans.lean:5:  value : α
PrefixScans.lean:6:  work : Nat
PrefixScans.lean:7:  deriving Repr
```

## source-PrefixScans-containsMeter.txt

```text
PrefixScans.lean:11: def containsMeter (x : Nat) : List Nat→Measured Bool
PrefixScans.lean:12:  | []=>⟨false,1⟩
PrefixScans.lean:13:  | y::ys=>if x==y then ⟨true,2⟩ else
PrefixScans.lean:14:           let r:=containsMeter x ys;⟨r.value,r.work+2⟩
```

## source-PrefixScans-nodupMeter.txt

```text
PrefixScans.lean:40: def nodupMeter : List Nat→Measured Bool
PrefixScans.lean:41:  | []=>⟨true,1⟩
PrefixScans.lean:42:  | x::xs=>let r:=nodupMeter xs
PrefixScans.lean:43:           if r.value then let c:=containsMeter x xs;⟨!c.value,r.work+c.work+1⟩
PrefixScans.lean:44:           else ⟨false,r.work+1⟩
```

## source-Pretest-Result.txt

```text
Pretest.lean:37: inductive Result where
Pretest.lean:38:   | refused
Pretest.lean:39:   | rejected
Pretest.lean:40:   | found (cut : Option Vertex)
Pretest.lean:41:   deriving DecidableEq, Repr
```

## source-Pretest-edges_subtreeLabels.txt

```text
Pretest.lean:12: def edges : Tree → List Vertex
Pretest.lean:13:   | .leaf _ => []
Pretest.lean:14:   | .node l r => (vertices l).map (false :: ·) ++ (vertices r).map (true :: ·)

Pretest.lean:16: def subtreeLabels (S : Tree) (p : Vertex) : List Nat :=
Pretest.lean:17:   match subtree S p with
Pretest.lean:18:   | none => []
Pretest.lean:19:   | some s => leaves s
```

## source-Pretest-vertices.txt

```text
Pretest.lean:8: def vertices : Tree → List Vertex
Pretest.lean:9:   | .leaf _ => [[]]
Pretest.lean:10:   | .node l r => [] :: ((vertices l).map (false :: ·) ++ (vertices r).map (true :: ·))
```

## source-ProperPairWork-allPairMeter_nodupTreeMeter.txt

```text
ProperPairWork.lean:5: def nodupTreeMeter (T : Tree) : Measured Bool :=
ProperPairWork.lean:6:  let l:=leavesMeter T;let d:=nodupMeter l.value
ProperPairWork.lean:7:  ⟨d.value,l.work+d.work+1⟩

ProperPairWork.lean:21: def allPairMeter (T S : Tree) : Measured Bool :=
ProperPairWork.lean:22:  let l:=leavesMeter T;let a:=allTreeMeter S l.value
ProperPairWork.lean:23:  ⟨a.value,l.work+a.work+1⟩
```

## source-ProperPairWork-allTreeMeter.txt

```text
ProperPairWork.lean:15: def allTreeMeter (S : Tree) : List Nat→Measured Bool
ProperPairWork.lean:16:  | []=>⟨true,1⟩
ProperPairWork.lean:17:  | x::xs=>let c:=containsTreeMeter S x
ProperPairWork.lean:18:           if c.value then let r:=allTreeMeter S xs;⟨r.value,c.work+r.work+1⟩
ProperPairWork.lean:19:           else ⟨false,c.work+1⟩
```

## source-ProperPairWork-containsTreeMeter_properPairMeter.txt

```text
ProperPairWork.lean:9: def containsTreeMeter (T : Tree) (x : Nat) : Measured Bool :=
ProperPairWork.lean:10:  let l:=leavesMeter T;let d:=containsMeter x l.value
ProperPairWork.lean:11:  ⟨d.value,l.work+d.work+1⟩

ProperPairWork.lean:73: def properPairMeter (T S : Tree) : Measured Bool :=
ProperPairWork.lean:74:  let a:=nodupTreeMeter T
ProperPairWork.lean:75:  if a.value then
ProperPairWork.lean:76:   let b:=nodupTreeMeter S
ProperPairWork.lean:77:   if b.value then
ProperPairWork.lean:78:    let c:=allPairMeter T S
ProperPairWork.lean:79:    if c.value then
ProperPairWork.lean:80:     let d:=allPairMeter S T
ProperPairWork.lean:81:     ⟨d.value,a.work+b.work+c.work+d.work+4⟩
ProperPairWork.lean:82:    else ⟨false,a.work+b.work+c.work+3⟩
ProperPairWork.lean:83:   else ⟨false,a.work+b.work+2⟩
ProperPairWork.lean:84:  else ⟨false,a.work+1⟩
```

## source-QueryCaller-Job_Receipt_schedule.txt

```text
QueryCaller.lean:5: inductive Job (P A : Type) where
QueryCaller.lean:6:   | resolved (problem : P) (cost : Nat) (answer : A)
QueryCaller.lean:7:   | hard (problem : P)
QueryCaller.lean:8:   deriving Repr

QueryCaller.lean:26: structure Receipt (A : Type) where
QueryCaller.lean:27:   answers : Option (List (Nat × A))
QueryCaller.lean:28:   calls : List Nat
QueryCaller.lean:29:   visits : Nat
QueryCaller.lean:30:   deriving Repr

QueryCaller.lean:47: def schedule (solve : P → Nat → Option (Nat × A)) (q : Nat)
QueryCaller.lean:48:     (js : List (Job P A)) : Receipt A :=
QueryCaller.lean:49:   if q < knownCost js + 2*pending js then ⟨none, [], 0⟩ else
QueryCaller.lean:50:     let r := run solve (allocated q js) js
QueryCaller.lean:51:     ⟨r.answers.bind (fun xs => if answerCost xs ≤ q then some xs else none),
QueryCaller.lean:52:       r.calls, r.visits⟩
```

## source-QueryCaller-allocated_answerCost_knownCost_pending_run.txt

```text
QueryCaller.lean:14: def knownCost : List (Job P A) → Nat
QueryCaller.lean:15:   | [] => 0
QueryCaller.lean:16:   | .resolved _ c _ :: js => c + knownCost js
QueryCaller.lean:17:   | .hard _ :: js => knownCost js

QueryCaller.lean:19: def pending : List (Job P A) → Nat
QueryCaller.lean:20:   | [] => 0
QueryCaller.lean:21:   | .resolved _ _ _ :: js => pending js
QueryCaller.lean:22:   | .hard _ :: js => 1 + pending js

QueryCaller.lean:24: def answerCost (xs : List (Nat × A)) : Nat := (xs.map Prod.fst).sum

QueryCaller.lean:32: def run (solve : P → Nat → Option (Nat × A)) (b : Nat) : List (Job P A) → Receipt A
QueryCaller.lean:33:   | [] => ⟨some [], [], 0⟩
QueryCaller.lean:34:   | .resolved _ c a :: js =>
QueryCaller.lean:35:     let r := run solve b js
QueryCaller.lean:36:     ⟨r.answers.map ((c,a) :: ·), r.calls, r.visits+1⟩
QueryCaller.lean:37:   | .hard p :: js =>
QueryCaller.lean:38:     match solve p b with
QueryCaller.lean:39:     | none => ⟨none, [b], 1⟩
QueryCaller.lean:40:     | some x =>
QueryCaller.lean:41:       let r := run solve b js
QueryCaller.lean:42:       ⟨r.answers.map (x :: ·), b :: r.calls, r.visits+1⟩

QueryCaller.lean:44: def allocated (q : Nat) (js : List (Job P A)) : Nat :=
QueryCaller.lean:45:   q - knownCost js - 2*(pending js-1)
```

## source-RMAF-disjointVertices_sameShape.txt

```text
RMAF.lean:36: def sameShape : Tree → Tree → Bool
RMAF.lean:37:   | .leaf a, .leaf b => a == b
RMAF.lean:38:   | .node a b, .node c d =>
RMAF.lean:39:       (sameShape a c && sameShape b d) ||
RMAF.lean:40:       (sameShape a d && sameShape b c)
RMAF.lean:41:   | _, _ => false

RMAF.lean:135: def disjointVertices (a b : List Vertex) : Bool :=
RMAF.lean:136:   a.all (fun v => !(b.contains v))
```

## source-RMAF-minimalVertices_pairwiseEmbeddings_partitionCheck_prependSide_restrictionAgrees_rootedSpan.txt

```text
RMAF.lean:111: def prependSide (side : Bool) (vs : List Vertex) : List Vertex :=
RMAF.lean:112:   vs.map (side :: ·)

RMAF.lean:116: def rootedSpan (selected : List Nat) : Tree → List Vertex
RMAF.lean:117:   | .leaf x => if selected.contains x then [[]] else []
RMAF.lean:118:   | .node l r =>
RMAF.lean:119:       let ls := rootedSpan selected l
RMAF.lean:120:       let rs := rootedSpan selected r
RMAF.lean:121:       if ls.isEmpty && rs.isEmpty then []
RMAF.lean:122:       else [] :: (prependSide false ls ++ prependSide true rs)

RMAF.lean:126: def minimalVertices (selected : List Nat) : Tree → List Vertex
RMAF.lean:127:   | .leaf x => if selected.contains x then [[]] else []
RMAF.lean:128:   | .node l r =>
RMAF.lean:129:       let ls := rootedSpan selected l
RMAF.lean:130:       let rs := rootedSpan selected r
RMAF.lean:131:       if ls.isEmpty then prependSide true (minimalVertices selected r)
RMAF.lean:132:       else if rs.isEmpty then prependSide false (minimalVertices selected l)
RMAF.lean:133:       else [] :: (prependSide false ls ++ prependSide true rs)

RMAF.lean:138: def pairwiseEmbeddings (t : Tree) : List (List Nat) → Bool
RMAF.lean:139:   | [] => true
RMAF.lean:140:   | b :: bs =>
RMAF.lean:141:       bs.all (fun c => disjointVertices (minimalVertices b t) (minimalVertices c t)) &&
RMAF.lean:142:       pairwiseEmbeddings t bs

RMAF.lean:144: def restrictionAgrees (t u : Tree) (b : List Nat) : Bool :=
RMAF.lean:145:   match restrict b t, restrict b u with
RMAF.lean:146:   | some s, some v => sameShape s v
RMAF.lean:147:   | _, _ => false

RMAF.lean:149: def partitionCheck (labels : List Nat) (bs : List (List Nat)) : Bool :=
RMAF.lean:150:   bs.all (fun b => !b.isEmpty) &&
RMAF.lean:151:   labels.all (fun x => bs.flatten.count x == 1) &&
RMAF.lean:152:   bs.flatten.all (fun x => labels.contains x)
```

## source-RMAF-restrict.txt

```text
RMAF.lean:84: def restrict (selected : List Nat) : Tree → Option Tree
RMAF.lean:85:   | .leaf x => if selected.contains x then some (.leaf x) else none
RMAF.lean:86:   | .node l r =>
RMAF.lean:87:       match restrict selected l, restrict selected r with
RMAF.lean:88:       | none, none => none
RMAF.lean:89:       | some a, none => some a
RMAF.lean:90:       | none, some b => some b
RMAF.lean:91:       | some a, some b => some (.node a b)
```

## source-RWChoose-meterChoose.txt

```text
RWChoose.lean:21: def meterChoose (t : GTree) : Charged Choice :=
RWChoose.lean:22:  let g:=meterGroups t;let m:=meterMixed t
RWChoose.lean:23:  match g.value with
RWChoose.lean:24:  | []=>⟨.refuse "empty current source",g.work+m.work+8⟩
RWChoose.lean:25:  | first::_=>
RWChoose.lean:26:   let a:=meterAll (fun h:Group=>⟨h.color==first.color,4⟩) g.value
RWChoose.lean:27:   let f:=meterFind (meterUniqueTest g.value) g.value
RWChoose.lean:28:   ⟨if a.value then .finish else match f.value with
RWChoose.lean:29:     | some x=>.one x
RWChoose.lean:30:     | none=>match m.value with
RWChoose.lean:31:       | some (x,y)=>if x.color==y.color then .refuse "unnormalized homogeneous cherry" else .two x y
RWChoose.lean:32:       | none=>.refuse "no mixed cherry in multicolor source",
RWChoose.lean:33:     g.work+m.work+a.work+f.work+16⟩
```

## source-RWChoose-meterUniqueTest.txt

```text
RWChoose.lean:6: def meterUniqueTest (gs : List Group) (g : Group) : Charged Bool :=
RWChoose.lean:7:  let f:=meterFilter (fun h:Group=>⟨h.color==g.color,4⟩) gs
RWChoose.lean:8:  let n:=meterLength f.value
RWChoose.lean:9:  ⟨n.value==1,f.work+n.work+4⟩
```

## source-RWFinal-meterColor_meterRecover.txt

```text
RWFinal.lean:9: def meterColor : CommonForest→Nat→Charged Nat
RWFinal.lean:10:  | [],_=>⟨0,2⟩
RWFinal.lean:11:  | b::P,x=>let contains:=meterContains x b
RWFinal.lean:12:    if contains.value then ⟨b.headD 0,contains.work+8⟩
RWFinal.lean:13:    else let r:=meterColor P x;⟨r.value,contains.work+r.work+8⟩

RWFinal.lean:38: def meterRecover (S : Tree) (P : CommonForest) : Charged (Option Output) :=
RWFinal.lean:39:  let check:=meterInputCheck S P
RWFinal.lean:40:  if check.value then
RWFinal.lean:41:   let len:=meterLength P
RWFinal.lean:42:   let g:=meterGenerate S (meterColor P) (len.value-1)
RWFinal.lean:43:   ⟨g.value.outputs.head?,check.work+len.work+g.work+8⟩
RWFinal.lean:44:  else ⟨none,check.work+8⟩
```

## source-RWInitial-Built_InitialMeasured.txt

```text
RWInitial.lean:6: structure Built where
RWInitial.lean:7:  value : GTree
RWInitial.lean:8:  work : Nat
RWInitial.lean:9:  coloring : Nat

RWInitial.lean:34: structure InitialMeasured where
RWInitial.lean:35:  value : Option (Nat×GTree)
RWInitial.lean:36:  work : Nat
RWInitial.lean:37:  coloring : Nat
```

## source-RWInitial-meterBuild_meterInitial.txt

```text
RWInitial.lean:11: def meterBuild (color : Nat→Charged Nat) (p : RMAF.Vertex) : Tree→Built
RWInitial.lean:12:  | .leaf x=>let a:=color x;⟨.leaf ⟨p,[x],a.value⟩,a.work+8,a.work⟩
RWInitial.lean:13:  | .node l r=>let a:=meterBuild color (p++[false]) l;let b:=meterBuild color (p++[true]) r
RWInitial.lean:14:    ⟨.node p a.value b.value,a.work+b.work+8*(p.length+1)+8,a.coloring+b.coloring⟩

RWInitial.lean:39: def meterInitial (color : Nat→Charged Nat) (budget : Nat) (t : Tree) : InitialMeasured :=
RWInitial.lean:40:  let leaves1:=meterLeaves t;let proper:=meterNodup leaves1.value
RWInitial.lean:41:  if proper.value then
RWInitial.lean:42:   let leaves2:=meterLeaves t;let len:=meterLength leaves2.value
RWInitial.lean:43:   let built:=meterBuild color [] t
RWInitial.lean:44:   ⟨some (min budget (len.value-1),built.value),leaves1.work+proper.work+leaves2.work+len.work+built.work+16,built.coloring⟩
RWInitial.lean:45:  else ⟨none,leaves1.work+proper.work+8,0⟩
```

## source-RWInitial-meterGenerate.txt

```text
RWInitial.lean:82: def meterGenerate (t : Tree) (color : Nat→Charged Nat) (budget : Nat) : Charged Receipt :=
RWInitial.lean:83:  let init:=meterInitial color budget t
RWInitial.lean:84:  match init.value with
RWInitial.lean:85:  | none=>⟨⟨[],["duplicate original label"],0,0,0⟩,init.work+8⟩
RWInitial.lean:86:  | some (q,built)=>let r:=meterRun q built [] [];⟨r.value,init.work+r.work+8⟩
```

## source-RWLocal-meterAttempt_meterStep.txt

```text
RWLocal.lean:6: def meterAttempt (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
RWLocal.lean:7:  (t : GTree) (d : List Group) (c : List RMAF.Vertex) (g : Group) : Charged Receipt :=
RWLocal.lean:8:  let contains:=meterVertexContains g.origin c;let erased:=meterErase g.origin t
RWLocal.lean:9:  let fee:=contains.work+erased.work+16
RWLocal.lean:10:  if g.origin=[] then ⟨⟨[],["attempt to cut original root"],0,1,0⟩,fee⟩
RWLocal.lean:11:  else if contains.value then ⟨⟨[],["duplicate original source cut"],0,1,0⟩,fee⟩
RWLocal.lean:12:  else match erased.value with
RWLocal.lean:13:  | none=>⟨⟨[],["attempt removed entire current source"],0,1,0⟩,fee⟩
RWLocal.lean:14:  | some next=>let r:=f next (g::d) (g.origin::c)
RWLocal.lean:15:    ⟨{r.value with childAttempts:=r.value.childAttempts+1},fee+r.work+8⟩

RWLocal.lean:87: def meterStep (f : GTree→List Group→List RMAF.Vertex→Charged Receipt)
RWLocal.lean:88:  (current : GTree) (d : List Group) (c : List RMAF.Vertex) : Charged Receipt :=
RWLocal.lean:89:  let n:=meterNormalize current;let ch:=meterChoose n.value
RWLocal.lean:90:  match ch.value with
RWLocal.lean:91:  | .finish=>let o:=meterOutput n.value d c
RWLocal.lean:92:    ⟨⟨[o.value],[],1,0,0⟩,n.work+ch.work+o.work+32⟩
RWLocal.lean:93:  | .one g=>let a:=meterAttempt f n.value d c g
RWLocal.lean:94:    ⟨prefixRoot a.value,n.work+ch.work+a.work+32⟩
RWLocal.lean:95:  | .two a b=>let x:=meterAttempt f n.value d c a;let y:=meterAttempt f n.value d c b
RWLocal.lean:96:    ⟨prefixRoot (combine x.value y.value),n.work+ch.work+x.work+y.work+4*(appendCells x.value+1)+32⟩
RWLocal.lean:97:  | .refuse why=>⟨⟨[],[why],1,0,0⟩,n.work+ch.work+32⟩
```

## source-RWLocal-meterOutput.txt

```text
RWLocal.lean:58: def meterOutput (t : GTree) (d : List Group) (c : List RMAF.Vertex) : Charged Output :=
RWLocal.lean:59:  let ds:=meterMap (fun g:Group=>⟨g.labels,2⟩) d
RWLocal.lean:60:  let gs:=meterGroups t
RWLocal.lean:61:  let flat:=meterFlatMap (fun g:Group=>⟨g.labels,2⟩) gs.value
RWLocal.lean:62:  ⟨⟨ds.value++[flat.value],c⟩,ds.work+gs.work+flat.work+4*(ds.value.length+1)+12⟩
```

## source-RWRun-meterRun.txt

```text
RWRun.lean:8: def meterRun : Nat→GTree→List Group→List RMAF.Vertex→Charged Receipt
RWRun.lean:9:  | 0=>meterStep (fun _ _ _=>⟨⟨[],[],0,0,1⟩,4⟩)
RWRun.lean:10:  | q+1=>meterStep (meterRun q)
```

## source-RWTree-meterErase_meterGroups_meterNormalize.txt

```text
RWTree.lean:8: def meterGroups : GTree→Charged (List Group)
RWTree.lean:9:  | .leaf g=>⟨[g],4⟩
RWTree.lean:10:  | .node _ l r=>let a:=meterGroups l;let b:=meterGroups r
RWTree.lean:11:    ⟨a.value++b.value,a.work+b.work+4*(a.value.length+1)+4⟩

RWTree.lean:28: def meterNormalize : GTree→Charged GTree
RWTree.lean:29:  | .leaf g=>⟨.leaf g,4⟩
RWTree.lean:30:  | .node p l r=>let a:=meterNormalize l;let b:=meterNormalize r
RWTree.lean:31:    ⟨match a.value,b.value with
RWTree.lean:32:     | .leaf x,.leaf y=>if x.color=y.color then .leaf ⟨p,x.labels++y.labels,x.color⟩ else .node p (.leaf x) (.leaf y)
RWTree.lean:33:     | x,y=>.node p x y,
RWTree.lean:34:     a.work+b.work+normalizeFee a.value b.value⟩

RWTree.lean:54: def meterErase (chosen : RMAF.Vertex) : GTree→Charged (Option GTree)
RWTree.lean:55:  | .leaf g=>let e:=meterAddressEq g.origin chosen
RWTree.lean:56:    ⟨if e.value then none else some (.leaf g),e.work+8⟩
RWTree.lean:57:  | .node p l r=>let e:=meterAddressEq p chosen;let a:=meterErase chosen l;let b:=meterErase chosen r
RWTree.lean:58:    ⟨if e.value then none else match a.value,b.value with
RWTree.lean:59:     | none,none=>none | some x,none=>some x | none,some y=>some y | some x,some y=>some (.node p x y),
RWTree.lean:60:     e.work+a.work+b.work+12⟩
```

## source-RWTree-meterMixed_normalizeFee.txt

```text
RWTree.lean:24: def normalizeFee : GTree→GTree→Nat
RWTree.lean:25:  | .leaf a,.leaf _=>4*(a.labels.length+1)+12
RWTree.lean:26:  | _,_=>8

RWTree.lean:79: def meterMixed : GTree→Charged (Option (Group×Group))
RWTree.lean:80:  | .leaf _=>⟨none,2⟩
RWTree.lean:81:  | .node _ l r=>let a:=meterMixed l;let b:=meterMixed r
RWTree.lean:82:    ⟨match l,r with | .leaf x,.leaf y=>some (x,y) | _,_=>a.value.or b.value,a.work+b.work+8⟩
```

## source-Rename-relabel_relabelForest_swap.txt

```text
Rename.lean:5: def relabel (f : Nat → Nat) : Tree → Tree
Rename.lean:6:   | .leaf x => .leaf (f x)
Rename.lean:7:   | .node a b => .node (relabel f a) (relabel f b)

Rename.lean:9: def relabelForest (f : Nat → Nat) (F : List (List Nat)) := F.map (List.map f)

Rename.lean:11: def swap (a b x : Nat) := if x=a then b else if x=b then a else x
```

## source-Rule4CallerSource-leafAddressMeter_rule4PartitionMeter.txt

```text
Rule4CallerSource.lean:19: def rule4PartitionMeter (S : Tree) (cuts : List RMAF.Vertex) : Charged (List (List Nat)) :=
Rule4CallerSource.lean:20:  let b:=blocksMeter S cuts;let l:=meterLeaves S
Rule4CallerSource.lean:21:  let c:=meterFilter (rule4OutsideMeter S cuts) l.value
Rule4CallerSource.lean:22:  ⟨b.value++[c.value],b.work+l.work+c.work+b.value.length+4⟩

Rule4CallerSource.lean:29: def leafAddressMeter (a : Nat) : Tree→Charged (Option RMAF.Vertex)
Rule4CallerSource.lean:30:  | .leaf x=>⟨if x=a then some [] else none,4⟩
Rule4CallerSource.lean:31:  | .node l r=>let p:=leafAddressMeter a l
Rule4CallerSource.lean:32:   match p.value with
Rule4CallerSource.lean:33:   | some v=>⟨some (false::v),p.work+4⟩
Rule4CallerSource.lean:34:   | none=>let q:=leafAddressMeter a r;⟨q.value.map (true::·),p.work+q.work+4⟩
```

## source-Rule4CallerSource-rule4BranchesMeter_rule4StateMeter.txt

```text
Rule4CallerSource.lean:45: def rule4BranchesMeter {T S : Tree} (s : Rule4.Choice T S) : Charged (List Rule4.Branch) :=
Rule4CallerSource.lean:46:  let a:=leafAddressMeter s.raw.a S;let p:=cutsMeter T s.raw.a s.raw.c
Rule4CallerSource.lean:47:  ⟨[⟨T,S,[s.raw.cHead,s.raw.xHead],false⟩,
Rule4CallerSource.lean:48:    ⟨T,S,[a.value.getD []],false⟩,
Rule4CallerSource.lean:49:    ⟨S,T,p.value,true⟩],a.work+p.work+18⟩

Rule4CallerSource.lean:57: def rule4StateMeter (b : Rule4.Branch) : Charged (List Tree) :=
Rule4CallerSource.lean:58:  let p:=rule4PartitionMeter b.source b.cuts
Rule4CallerSource.lean:59:  let f:=sourceForestMeter b.source p.value
Rule4CallerSource.lean:60:  ⟨f.value,p.work+f.work+4⟩
```

## source-Rule4CallerSource-rule4OutsideMeter.txt

```text
Rule4CallerSource.lean:11: def rule4OutsideMeter (S : Tree) (cuts : List RMAF.Vertex) (x : Nat) : Charged Bool :=
Rule4CallerSource.lean:12:  meterAll (fun p=>let s:=subtreeLabelsMeter S p;let c:=meterContains x s.value
Rule4CallerSource.lean:13:   ⟨!c.value,s.work+c.work+2⟩) cuts
```

## source-Rule4Program-Branch.txt

```text
Rule4Program.lean:68: structure Branch where
Rule4Program.lean:69:   target : Tree
Rule4Program.lean:70:   source : Tree
Rule4Program.lean:71:   cuts : List RMAF.Vertex
Rule4Program.lean:72:   swapped : Bool
Rule4Program.lean:73:   deriving Repr
```

## source-Rule4Selector-Choice_LocalGuard_Priority_RawChoice.txt

```text
Rule4Selector.lean:40: def Priority (T S : Tree) : Prop :=
Rule4Selector.lean:41:   (leaves T).Nodup ∧ (leaves S).Nodup ∧ (leaves T).Perm (leaves S) ∧
Rule4Selector.lean:42:   (orderedCherries T).all (fun p => !(orderedCherries S).contains p) = true ∧
Rule4Selector.lean:43:   (orderedCherries T).all (fun p => (pendantOriginal S p.1 p.2).length != 1) = true ∧
Rule4Selector.lean:44:   (orderedCherries S).all (fun p => (pendantOriginal T p.1 p.2).length != 1) = true

Rule4Selector.lean:48: structure RawChoice where
Rule4Selector.lean:49:   a : Nat
Rule4Selector.lean:50:   b : Nat
Rule4Selector.lean:51:   c : Nat
Rule4Selector.lean:52:   cHead : RMAF.Vertex
Rule4Selector.lean:53:   xHead : RMAF.Vertex
Rule4Selector.lean:54:   deriving Repr, DecidableEq

Rule4Selector.lean:56: def LocalGuard (T S : Tree) (s : RawChoice) : Prop :=
Rule4Selector.lean:57:   (s.a,s.b) ∈ orderedCherries T ∧ (s.a,s.c) ∈ orderedCherries S ∧ s.a ≠ s.b ∧
Rule4Selector.lean:58:   (pendantOriginal S s.a s.b).Perm [s.cHead,s.xHead] ∧ subtreeLabels S s.cHead = [s.c]

Rule4Selector.lean:64: structure Choice (T S : Tree) where
Rule4Selector.lean:65:   raw : RawChoice
Rule4Selector.lean:66:   priority : Priority T S
Rule4Selector.lean:67:   admission : LocalGuard T S raw
```

## source-Rule4Selector-orderedCherries.txt

```text
Rule4Selector.lean:6: def orderedCherries : Tree → List (Nat × Nat)
Rule4Selector.lean:7:   | .leaf _ => []
Rule4Selector.lean:8:   | .node l r =>
Rule4Selector.lean:9:     (match l,r with | .leaf a,.leaf b => [(a,b),(b,a)] | _,_ => []) ++
Rule4Selector.lean:10:       orderedCherries l ++ orderedCherries r
```

## source-Rule5Defs-incident_properPair.txt

```text
Rule5Defs.lean:19: def properPair (T S : Tree) : Bool :=
Rule5Defs.lean:20:  decide (leaves T).Nodup && decide (leaves S).Nodup &&
Rule5Defs.lean:21:  (leaves T).all (leaves S).contains && (leaves S).all (leaves T).contains

Rule5Defs.lean:32: def incident (T : Tree) (X : List Nat) : List RMAF.Vertex :=
Rule5Defs.lean:33:  (vertices T).filter fun q => !q.isEmpty &&
Rule5Defs.lean:34:    ((minimalVertices X T).contains q != (minimalVertices X T).contains q.dropLast)
```

## source-Rule5SelectedSource-dispatchSource.txt

```text
Rule5SelectedSource.lean:60: def dispatchSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
Rule5SelectedSource.lean:61:  (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : Charged Result :=
Rule5SelectedSource.lean:62:  let c:=finalMeter classFee T S a b
Rule5SelectedSource.lean:63:  match c.value with
Rule5SelectedSource.lean:64:  | none=>⟨.selectorRefused,c.work+2⟩
Rule5SelectedSource.lean:65:  | some z=>let r:=runSelectedSource cb W classFee literalFee T S a b q z;⟨r.value,c.work+r.work+2⟩
```

## source-Rule5SelectedSource-runSelectedSource.txt

```text
Rule5SelectedSource.lean:10: def runSelectedSource (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
Rule5SelectedSource.lean:11:  (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) : FinalSelection→Charged Result
Rule5SelectedSource.lean:12:  | .prefix s=>let r:=selectedArmSource cb W T S a b q (.prefix s);⟨.answered r.value,r.work+2⟩
Rule5SelectedSource.lean:13:  | .remaining d (.first u v)=>let r:=selectedArmSource cb W T S a b q (.remaining d (.first u v));⟨.answered r.value,r.work+2⟩
Rule5SelectedSource.lean:14:  | .remaining d (.third u v)=>let r:=selectedArmSource cb W T S a b q (.remaining d (.third u v));⟨.answered r.value,r.work+2⟩
Rule5SelectedSource.lean:15:  | .remaining d (.one _)=>let r:=commonSource cb W T S a b d q;⟨.answered r.value,r.work+2⟩
Rule5SelectedSource.lean:16:  | .remaining _ (.second _ _)=>
Rule5SelectedSource.lean:17:   let r:=paidSelectedSource cb W classFee literalFee T S a b q
Rule5SelectedSource.lean:18:   ⟨match r.value with | .builderRefused=>.paidBuilderRefused | .answered F=>.answered F,r.work+2⟩
```

## source-Safety-ActualCherry.txt

```text
Safety.lean:126: def ActualCherry (T : Tree) (a b : Nat) : Prop :=
Safety.lean:127:   ∃ p, CherryAt T p a b ∨ CherryAt T p b a
```

## source-SchedulerAtoms-allocatedMeter_knownCostMeter_pendingMeter_postChargeMeter.txt

```text
SchedulerAtoms.lean:5: def knownCostMeter {P A : Type} : List (Job P A)→Charged Nat
SchedulerAtoms.lean:6:  | []=>⟨0,2⟩
SchedulerAtoms.lean:7:  | .resolved _ c _::js=>let r:=knownCostMeter js;⟨c+r.value,r.work+8⟩
SchedulerAtoms.lean:8:  | .hard _::js=>let r:=knownCostMeter js;⟨r.value,r.work+8⟩

SchedulerAtoms.lean:18: def pendingMeter {P A : Type} : List (Job P A)→Charged Nat
SchedulerAtoms.lean:19:  | []=>⟨0,2⟩
SchedulerAtoms.lean:20:  | .resolved _ _ _::js=>let r:=pendingMeter js;⟨r.value,r.work+8⟩
SchedulerAtoms.lean:21:  | .hard _::js=>let r:=pendingMeter js;⟨1+r.value,r.work+8⟩

SchedulerAtoms.lean:39: def allocatedMeter {P A : Type} (q : Nat) (js : List (Job P A)) : Charged Nat:=
SchedulerAtoms.lean:40:  let k:=knownCostMeter js;let p:=pendingMeter js
SchedulerAtoms.lean:41:  ⟨q-k.value-2*(p.value-1),k.work+p.work+8⟩

SchedulerAtoms.lean:49: def postChargeMeter {A : Type} (r : Receipt A) : Charged Nat:=
SchedulerAtoms.lean:50:  match r.answers with | none=>⟨4,4⟩ | some xs=>⟨4*xs.length+4,xs.length+8⟩
```

## source-SchedulerAtoms-answerCostMeter.txt

```text
SchedulerAtoms.lean:31: def answerCostMeter {A : Type} : List (Nat×A)→Charged Nat
SchedulerAtoms.lean:32:  | []=>⟨0,2⟩
SchedulerAtoms.lean:33:  | x::xs=>let r:=answerCostMeter xs;⟨x.1+r.value,r.work+8⟩
```

## source-SchedulerRun-runSourceMeter.txt

```text
SchedulerRun.lean:8: def runSourceMeter {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
SchedulerRun.lean:9:  (b : Nat) : List (Job P A)→MeterReceipt P A
SchedulerRun.lean:10:  | []=>⟨⟨some [],[],0⟩,[],2,0⟩
SchedulerRun.lean:11:  | .resolved _ c a::js=>let r:=runSourceMeter f b js
SchedulerRun.lean:12:    ⟨⟨r.value.answers.map ((c,a)::·),r.value.calls,r.value.visits+1⟩,
SchedulerRun.lean:13:      r.queries,r.callerWork+32,r.recursiveWork⟩
SchedulerRun.lean:14:  | .hard p::js=>let x:=f p b
SchedulerRun.lean:15:    match x.value with
SchedulerRun.lean:16:    | none=>⟨⟨none,[b],1⟩,[(p,b)],32,x.work⟩
SchedulerRun.lean:17:    | some a=>let r:=runSourceMeter f b js
SchedulerRun.lean:18:      ⟨⟨r.value.answers.map (a::·),b::r.value.calls,r.value.visits+1⟩,
SchedulerRun.lean:19:        (p,b)::r.queries,r.callerWork+32,x.work+r.recursiveWork⟩
```

## source-SchedulerSchedule-acceptAnswersMeter.txt

```text
SchedulerSchedule.lean:5: def acceptAnswersMeter {A : Type} (q : Nat) : Option (List (Nat×A))→Charged (Option (List (Nat×A)))
SchedulerSchedule.lean:6:  | none=>⟨none,4⟩
SchedulerSchedule.lean:7:  | some xs=>let a:=answerCostMeter xs
SchedulerSchedule.lean:8:    ⟨if a.value≤q then some xs else none,a.work+8⟩
```

## source-SchedulerSchedule-scheduleSourceMeter.txt

```text
SchedulerSchedule.lean:16: def scheduleSourceMeter {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
SchedulerSchedule.lean:17:  (q : Nat) (js : List (Job P A)) : MeterReceipt P A:=
SchedulerSchedule.lean:18:  let k:=knownCostMeter js;let p:=pendingMeter js
SchedulerSchedule.lean:19:  if q<k.value+2*p.value then ⟨⟨none,[],0⟩,[],k.work+p.work+js.length+24,0⟩ else
SchedulerSchedule.lean:20:  let b:=allocatedMeter q js
SchedulerSchedule.lean:21:  let r:=runSourceMeter f b.value js
SchedulerSchedule.lean:22:  let a:=acceptAnswersMeter q r.value.answers
SchedulerSchedule.lean:23:  let pc:=postChargeMeter r.value
SchedulerSchedule.lean:24:  ⟨⟨a.value,r.value.calls,r.value.visits⟩,r.queries,
SchedulerSchedule.lean:25:    k.work+p.work+b.work+r.callerWork+a.work+pc.work+js.length+40,r.recursiveWork⟩
```

## source-SelectedAgreementBinding-selectedArmSource.txt

```text
SelectedAgreementBinding.lean:25: def selectedArmSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
SelectedAgreementBinding.lean:26:  (T S : Tree) (a b q : Nat) (z : FinalSelection) : WholeSourceWork.Charged (Option (List (List Nat))) :=
SelectedAgreementBinding.lean:27:  let cs:=selectedChildrenMeter S a b z
SelectedAgreementBinding.lean:28:  let r:=runChildrenSource actual W T S q cs.value
SelectedAgreementBinding.lean:29:  ⟨r.value,cs.work+r.work+2⟩
```

## source-SelectedChildrenWork-selectedChildrenMeter.txt

```text
SelectedChildrenWork.lean:8: def selectedChildrenMeter (S : Tree) (a b : Nat) : FinalSelection→Measured (List Child)
SelectedChildrenWork.lean:9:  | .prefix s=>localChildrenMeter S a b s
SelectedChildrenWork.lean:10:  | .remaining d (.first _ _)=>firstChildrenMeter S a b d
SelectedChildrenWork.lean:11:  | .remaining d (.third _ _)=>thirdChildrenMeter S a b d
SelectedChildrenWork.lean:12:  | _=>⟨[],1⟩
```

## source-SelectedExact-SelectedResult.txt

```text
SelectedExact.lean:9: inductive SelectedResult where
SelectedExact.lean:10:  | builderRefused
SelectedExact.lean:11:  | answered (answer : Option Forest)
SelectedExact.lean:12:  deriving DecidableEq, Repr
```

## source-SelectedRestriction-makeChildMeter_sourceForestMeter.txt

```text
SelectedRestriction.lean:11: def sourceForestMeter (S : Tree) : List (List Nat)→Measured (List Tree)
SelectedRestriction.lean:12:  | []=>⟨[],1⟩
SelectedRestriction.lean:13:  | B::P=>let t:=meterRestrict B S;let r:=sourceForestMeter S P
SelectedRestriction.lean:14:            ⟨match t.value with | none=>r.value | some U=>U::r.value,t.work+r.work+3⟩

SelectedRestriction.lean:51: def makeChildMeter (S : Tree) (P : List (List Nat)) (paid : Nat) : Measured Child :=
SelectedRestriction.lean:52:  let fs:=sourceForestMeter S P;⟨⟨P,fs.value,paid⟩,fs.work+4⟩
```

## source-SelectedRestriction-pendantChildMeter.txt

```text
SelectedRestriction.lean:67: def pendantChildMeter (S : Tree) (a b : Nat) : Measured Child :=
SelectedRestriction.lean:68:  let p:=partitionMeter S a b;let c:=cutsMeter S a b
SelectedRestriction.lean:69:  let child:=makeChildMeter S p.value c.value.length
SelectedRestriction.lean:70:  ⟨child.value,p.work+c.work+c.value.length+child.work+2⟩
```

## source-Selector-Choice.txt

```text
Selector.lean:531: inductive Choice where
Selector.lean:532:   | vertex : Vertex → Choice
Selector.lean:533:   | edge : (Vertex × Vertex) → Choice
Selector.lean:534:   deriving DecidableEq, Repr
```

## source-Selector-vertices.txt

```text
Selector.lean:287: def vertices : RMAF.Tree → List Vertex
Selector.lean:288:   | .leaf _ => [[]]
Selector.lean:289:   | .node l r => [] :: (RMAF.prependSide false (vertices l) ++ RMAF.prependSide true (vertices r))
```

## source-SelectorBuilder-BottomData.txt

```text
SelectorBuilder.lean:7: structure BottomData where
SelectorBuilder.lean:8:  w : RMAF.Vertex
SelectorBuilder.lean:9:  sa : Bool
SelectorBuilder.lean:10:  sc : Bool
SelectorBuilder.lean:11:  sb : Bool
SelectorBuilder.lean:12:  a : Nat
SelectorBuilder.lean:13:  b : Nat
SelectorBuilder.lean:14:  X : Tree
SelectorBuilder.lean:15:  deriving DecidableEq, Repr
```

## source-SelectorBuilder-LiteralProps.txt

```text
SelectorBuilder.lean:43: def LiteralProps (T S : Tree) (a b : Nat) (d : BadSelection) (u v : RMAF.Vertex)
SelectorBuilder.lean:44:  (R : BottomData) (C : Tree) (qa ub : RMAF.Vertex) : Prop :=
SelectorBuilder.lean:45:  properPair T S=true ∧
SelectorBuilder.lean:46:  subtree S R.w=some (bottom R.sa R.sc R.sb R.a R.b d.c R.X) ∧
SelectorBuilder.lean:47:  (∃ i∈HardParent.vertices T, CherryAt T i R.a R.b ∨ CherryAt T i R.b R.a) ∧
SelectorBuilder.lean:48:  (cuts S R.a R.b).length=2 ∧
SelectorBuilder.lean:49:  (∀ z∈leaves T, z∈leaves C ↔ z∉leaves R.X ∧ z≠d.c) ∧
SelectorBuilder.lean:50:  R.b∈leaves C ∧ d.c∉leaves C ∧
SelectorBuilder.lean:51:  LeafAt T qa R.a ∧ LeafAt T ub R.b ∧ LeafAt T u d.c ∧
SelectorBuilder.lean:52:  (incident T (leaves R.X)=[v,u] ∨ incident T (leaves R.X)=[u,v]) ∧
SelectorBuilder.lean:53:  v.dropLast∈minimalVertices (leaves R.X) T ∧ u.dropLast∈minimalVertices (leaves R.X) T ∧
SelectorBuilder.lean:54:  v∉minimalVertices (leaves R.X) T ∧ u∉minimalVertices (leaves R.X) T ∧
SelectorBuilder.lean:55:  subtreeLabels S d.badArc=leaves R.X ∧ EndpointOrder a b R.a R.b
```

## source-SelectorBuilder-SelectedPaid.txt

```text
SelectorBuilder.lean:84: structure SelectedPaid (T S : Tree) where
SelectorBuilder.lean:85:  d : BadSelection
SelectorBuilder.lean:86:  u : RMAF.Vertex
SelectorBuilder.lean:87:  v : RMAF.Vertex
SelectorBuilder.lean:88:  geometry : LiteralGeometry T S
```

## source-SelectorBuilder-leafAddress?.txt

```text
SelectorBuilder.lean:40: def leafAddress? (T : Tree) (a : Nat) : Option RMAF.Vertex :=
SelectorBuilder.lean:41:  (HardParent.vertices T).find? (fun q => decide (LeafAt T q a))
```

## source-SelectorBuilder-unorient.txt

```text
SelectorBuilder.lean:17: def unorient (s : Bool) : Tree → Option (Tree × Tree)
SelectorBuilder.lean:18:  | .leaf _ => none
SelectorBuilder.lean:19:  | .node l r => some (if s then (r,l) else (l,r))
```

## source-SelectorGeometry-EndpointOrder.txt

```text
SelectorGeometry.lean:11: def EndpointOrder (a b x y : Nat) : Prop := (x=a ∧ y=b) ∨ (x=b ∧ y=a)
```

## source-SetupAtoms-bump.txt

```text
SetupAtoms.lean:8: def bump {α : Type} (k : Nat) (r : Measured α) : Measured α := ⟨r.value,k+r.work⟩
```

## source-SetupAtoms-eraseMeter_relabelMeter.txt

```text
SetupAtoms.lean:13: def eraseMeter (x : Nat) : List Nat→Measured (List Nat)
SetupAtoms.lean:14:  | []=>⟨[],1⟩
SetupAtoms.lean:15:  | y::ys=>if x==y then ⟨ys,2⟩ else let r:=eraseMeter x ys;⟨y::r.value,r.work+3⟩

SetupAtoms.lean:88: def relabelMeter (y rho : Nat) : Tree→Measured Tree
SetupAtoms.lean:89:  | .leaf x=>⟨.leaf (swap y rho x),4⟩
SetupAtoms.lean:90:  | .node l r=>let a:=relabelMeter y rho l;let b:=relabelMeter y rho r
SetupAtoms.lean:91:                ⟨.node a.value b.value,a.work+b.work+2⟩
```

## source-SetupAtoms-markedMeter_maxMeter_partitionTreeMeter_permMeter.txt

```text
SetupAtoms.lean:32: def permMeter : List Nat→List Nat→Measured Bool
SetupAtoms.lean:33:  | [],ys=>⟨ys.isEmpty,1⟩
SetupAtoms.lean:34:  | x::xs,ys=>let c:=containsMeter x ys
SetupAtoms.lean:35:               if c.value then let e:=eraseMeter x ys;let r:=permMeter xs e.value
SetupAtoms.lean:36:                               ⟨r.value,c.work+e.work+r.work+2⟩
SetupAtoms.lean:37:               else ⟨false,c.work+1⟩

SetupAtoms.lean:60: def partitionTreeMeter (T : Tree) (X Y : List Nat) : Measured Bool :=
SetupAtoms.lean:61:  let l:=leavesMeter T;let p:=meterPartition l.value [X,Y]
SetupAtoms.lean:62:  ⟨p.value,l.work+p.work+3⟩

SetupAtoms.lean:77: def maxMeter : List Nat→Measured Nat
SetupAtoms.lean:78:  | []=>⟨0,1⟩
SetupAtoms.lean:79:  | x::xs=>let r:=maxMeter xs;⟨max x r.value,r.work+3⟩

SetupAtoms.lean:100: def markedMeter (T : Tree) (X : List Nat) (y rho : Nat) : Measured (Option Tree) :=
SetupAtoms.lean:101:  let r:=meterRestrict (y::X) T
SetupAtoms.lean:102:  match r.value with
SetupAtoms.lean:103:  | none=>⟨none,r.work+2⟩
SetupAtoms.lean:104:  | some U=>let a:=relabelMeter y rho U;⟨some a.value,r.work+a.work+3⟩
```

## source-SiblingChildrenWork-firstChildrenMeter_thirdChildrenMeter.txt

```text
SiblingChildrenWork.lean:74: def firstChildrenMeter (S : Tree) (a b : Nat) (d : BadSelection) : Measured (List Child) :=
SiblingChildrenWork.lean:75:  let e:=siblingEndpointMeter S d.badArc
SiblingChildrenWork.lean:76:  match e.value with
SiblingChildrenWork.lean:77:  | none=>⟨[],e.work+1⟩
SiblingChildrenWork.lean:78:  | some x=>let s:=singletonChildMeter S x;let p:=pendantChildMeter S a b
SiblingChildrenWork.lean:79:   ⟨[s.value,p.value],e.work+s.work+p.work+3⟩

SiblingChildrenWork.lean:81: def thirdChildrenMeter (S : Tree) (a b : Nat) (d : BadSelection) : Measured (List Child) :=
SiblingChildrenWork.lean:82:  let e:=siblingEndpointMeter S d.badArc
SiblingChildrenWork.lean:83:  match e.value with
SiblingChildrenWork.lean:84:  | none=>⟨[],e.work+1⟩
SiblingChildrenWork.lean:85:  | some x=>let s:=singletonChildMeter S (if x=a then b else a);let p:=pendantChildMeter S a b
SiblingChildrenWork.lean:86:   ⟨[s.value,p.value],e.work+s.work+p.work+4⟩
```

## source-SiblingChildrenWork-reverseAuxMeter.txt

```text
SiblingChildrenWork.lean:6: def reverseAuxMeter : RMAF.Vertex→RMAF.Vertex→Measured RMAF.Vertex
SiblingChildrenWork.lean:7:  | [],acc=>⟨acc,1⟩
SiblingChildrenWork.lean:8:  | x::xs,acc=>let r:=reverseAuxMeter xs (x::acc);⟨r.value,r.work+2⟩
```

## source-SiblingChildrenWork-reverseMeter.txt

```text
SiblingChildrenWork.lean:22: def reverseMeter (p : RMAF.Vertex) :=reverseAuxMeter p []
```

## source-SiblingChildrenWork-siblingEndpointMeter.txt

```text
SiblingChildrenWork.lean:27: def siblingEndpointMeter (S : Tree) (q : RMAF.Vertex) : Measured (Option Nat) :=
SiblingChildrenWork.lean:28:  let rev:=reverseMeter q
SiblingChildrenWork.lean:29:  match rev.value with
SiblingChildrenWork.lean:30:  | []=>⟨none,rev.work+1⟩
SiblingChildrenWork.lean:31:  | side::parent=>let p:=reverseMeter parent;let t:=subtreeMeter S (p.value++[!side])
SiblingChildrenWork.lean:32:   ⟨match t.value with | some (.leaf x)=>some x | _=>none,rev.work+p.work+p.value.length+t.work+5⟩
```

## source-SolveCost-meterSolve.txt

```text
SolveCost.lean:5: def meterSolve (cs : List Nat) (owner : Nat→Charged Nat) (t : Tree) : Charged Paint :=
SolveCost.lean:6:  let tab := meterTable cs owner t
SolveCost.lean:7:  let pick := meterChoose meterChanges tab.value
SolveCost.lean:8:  ⟨pick.value,tab.work+pick.work+8⟩
```

## source-SourceBestMeter-sourceBestMeter.txt

```text
SourceBestMeter.lean:7: def sourceBestMeter {α : Type} (cost : α→Charged Nat) (valid : α→Charged Bool) : List α→Charged (Option α)
SourceBestMeter.lean:8:  | []=>⟨none,2⟩
SourceBestMeter.lean:9:  | x::xs=>let a:=valid x;let r:=sourceBestMeter cost valid xs
SourceBestMeter.lean:10:    if a.value then
SourceBestMeter.lean:11:     match r.value with
SourceBestMeter.lean:12:     | none=>⟨some x,a.work+r.work+8⟩
SourceBestMeter.lean:13:     | some y=>let cx:=cost x;let cy:=cost y
SourceBestMeter.lean:14:               ⟨if cx.value≤cy.value then some x else some y,a.work+r.work+cx.work+cy.work+12⟩
SourceBestMeter.lean:15:    else ⟨r.value,a.work+r.work+8⟩
```

## source-SourceOrientation-AX.txt

```text
SourceOrientation.lean:21: def AX (sa : Bool) (a : Nat) (X : Tree) := orient sa (.leaf a) X
```

## source-SourceOrientation-VC_orient.txt

```text
SourceOrientation.lean:7: def orient (s : Bool) (A B : Tree) : Tree := if s then .node B A else .node A B

SourceOrientation.lean:22: def VC (sa sc : Bool) (a c : Nat) (X : Tree) := orient sc (AX sa a X) (.leaf c)
```

## source-SourceOrientation-bArc.txt

```text
SourceOrientation.lean:27: def bArc (w : RMAF.Vertex) (sb : Bool) := w ++ [!sb]
```

## source-SourceOrientation-bottom.txt

```text
SourceOrientation.lean:23: def bottom (sa sc sb : Bool) (a b c : Nat) (X : Tree) := orient sb (VC sa sc a c X) (.leaf b)
```

## source-TableCost-meterRow.txt

```text
TableCost.lean:23: def meterRow (c : Nat) (ls rs : List Paint) : Charged Paint :=
TableCost.lean:24:  let a := meterChoose (meterEdgeCost c) ls
TableCost.lean:25:  let b := meterChoose (meterEdgeCost c) rs
TableCost.lean:26:  ⟨.node c a.value b.value,a.work+b.work+8⟩
```

## source-TableCost-meterTable.txt

```text
TableCost.lean:31: def meterTable (cs : List Nat) (owner : Nat→Charged Nat) : Tree→Charged (List Paint)
TableCost.lean:32:  | .leaf x => let o := owner x;⟨[.leaf x o.value],o.work+8⟩
TableCost.lean:33:  | .node l r =>
TableCost.lean:34:   let a := meterTable cs owner l
TableCost.lean:35:   let b := meterTable cs owner r
TableCost.lean:36:   let rows := cs.map (fun c=>meterRow c a.value b.value)
TableCost.lean:37:   ⟨rows.map Charged.value,a.work+b.work+(rows.map Charged.work).sum+8⟩
```

## source-TreeCheckMeters-meterRestrict_meterSameShape.txt

```text
TreeCheckMeters.lean:6: def meterSameShape : Tree → Tree → Charged Bool
TreeCheckMeters.lean:7:  | .leaf a,.leaf b => ⟨a==b,4⟩
TreeCheckMeters.lean:8:  | .node a b,.node c d =>
TreeCheckMeters.lean:9:   let ac:=meterSameShape a c;let bd:=meterSameShape b d;let ad:=meterSameShape a d;let bc:=meterSameShape b c
TreeCheckMeters.lean:10:   ⟨(ac.value && bd.value)||(ad.value && bc.value),ac.work+bd.work+ad.work+bc.work+4⟩
TreeCheckMeters.lean:11:  | _,_ => ⟨false,4⟩

TreeCheckMeters.lean:34: def meterRestrict (B : List Nat) : Tree → Charged (Option Tree)
TreeCheckMeters.lean:35:  | .leaf x => let m:=meterContains x B;⟨if m.value then some (.leaf x) else none,m.work+4⟩
TreeCheckMeters.lean:36:  | .node l r =>
TreeCheckMeters.lean:37:   let a:=meterRestrict B l;let b:=meterRestrict B r
TreeCheckMeters.lean:38:   ⟨match a.value,b.value with
TreeCheckMeters.lean:39:    | none,none=>none | some x,none=>some x | none,some y=>some y | some x,some y=>some (.node x y),a.work+b.work+4⟩
```

## source-TreeCheckMeters-meterRestrictionAgrees.txt

```text
TreeCheckMeters.lean:68: def meterRestrictionAgrees (T S : Tree) (B : List Nat) : Charged Bool :=
TreeCheckMeters.lean:69:  let a:=meterRestrict B T;let b:=meterRestrict B S
TreeCheckMeters.lean:70:  match a.value,b.value with
TreeCheckMeters.lean:71:  | some u,some v=>let c:=meterSameShape u v;⟨c.value,a.work+b.work+c.work+4⟩
TreeCheckMeters.lean:72:  | _,_=>⟨false,a.work+b.work+4⟩
```

## source-UnitCombineSource-combineSource.txt

```text
UnitCombineSource.lean:32: def combineSource (actual : GenericForest.FrontierWork.Ordinary) (W : OrdinaryWork)
UnitCombineSource.lean:33:  (T S : Tree) (a b q : Nat) (paid : Execution) : SourceExecution :=
UnitCombineSource.lean:34:  let cs:=unitChildrenMeter S a b
UnitCombineSource.lean:35:  let units:=runChildrenSource actual W T S q cs.value
UnitCombineSource.lean:36:  let calls:=unitCallsMeter S T a b q
UnitCombineSource.lean:37:  let best:=chooseMeter units.value paid.answer
UnitCombineSource.lean:38:  ⟨⟨best.value,calls.value++paid.calls⟩,
UnitCombineSource.lean:39:   cs.work+units.work+calls.work+best.work+calls.value.length+8⟩
```

## source-UnitCombineSource-unitCallsMeter_unitChildrenMeter.txt

```text
UnitCombineSource.lean:8: def unitChildrenMeter (S : Tree) (a b : Nat) : Rule5LocalWork.Measured (List CherryBranching.Child) :=
UnitCombineSource.lean:9:  let x:=singletonChildMeter S a;let y:=singletonChildMeter S b
UnitCombineSource.lean:10:  ⟨[x.value,y.value],x.work+y.work+3⟩

UnitCombineSource.lean:18: def unitCallsMeter (S T : Tree) (a b q : Nat) : Charged (List Call) :=
UnitCombineSource.lean:19:  let cs:=unitChildrenMeter S a b
UnitCombineSource.lean:20:  ⟨cs.value.filterMap (fun c=>(CherryBranching.remaining q c).map (fun r=>⟨some T,c.sourceForest,r⟩)),
UnitCombineSource.lean:21:   cs.work+8*cs.value.length+2⟩
```

## source-Work-Measured.txt

```text
Work.lean:121: structure Measured where
Work.lean:122:   receipt : Receipt
Work.lean:123:   work : Nat
Work.lean:124:   copied : Nat
Work.lean:125:   prunedCalls : Nat
Work.lean:126:   deriving Repr
```

## source-Work-appendCells.txt

```text
Work.lean:119: def appendCells (a : Receipt) : Nat := a.outputs.length + a.refusals.length
```

## ChildrenExecutionWork.runChildrenMeter

```text
ChildrenExecutionWork.lean:170: def runChildrenMeter (actual : Ordinary) (forestFee : ForestQuery→Nat) (agreementFee : Forest→Nat) (T S : Tree) (q : Nat) (cs : List Child) : ChildrenReceipt :=
ChildrenExecutionWork.lean:171:  let r:=childrenAnswersMeter actual forestFee T q cs
ChildrenExecutionWork.lean:172:  let b:=bestLengthMeter (acceptedMeter agreementFee T S q) r.value
ChildrenExecutionWork.lean:173:  ⟨b.value,r.localWork+b.work+r.value.length+2,r.recursiveWork,r.calls,r.value⟩
```

## Rule4Program.Branch.cost

```text
Rule4Program.lean:77: def Branch.cost (b : Branch) := b.cuts.length
```
