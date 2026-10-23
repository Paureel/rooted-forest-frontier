import SchedulerSchedule
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
open Universal233.BothBad

/-- The callback wrapper performs its two restrictions and the successful
F.length score locally. The forest computation itself is charged separately. -/
def mafRecursiveMeter (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (U : List Nat) (b : Nat) : Charged (Option (Nat×List (List Nat))):=
 let t:=meterRestrict U T;let s:=meterRestrict U S
 match t.value,s.value with
 | some t',some s'=>let a:=GenericForest.solve actual (some t') [s'] b
   ⟨a.map (fun F=>(F.length-1,F)),t.work+s.work+(a.map List.length).getD 0+12⟩
 | _,_=>⟨none,t.work+s.work+8⟩
@[simp] theorem mafRecursiveMeter_value (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (U : List Nat) (b : Nat) :
 (mafRecursiveMeter actual T S U b).value=MafScheduler.recursive T S (asTree (GenericForest.solve actual)) U b:=by
 simp only [mafRecursiveMeter,MafScheduler.recursive,meterRestrict_value,asTree]
 cases ht:restrict U T <;> cases hs:restrict U S <;> rfl

/-- This is a second restriction pass, performed by the original filterMap.
It is charged even though the callback already computed restrictions. -/
def ordinaryQueriesMeter (T S : Tree) : List (List Nat×Nat)→Charged (List Call)
 | []=>⟨[],2⟩
 | ub::qs=>let t:=meterRestrict ub.1 T;let s:=meterRestrict ub.1 S
   let r:=ordinaryQueriesMeter T S qs
   ⟨(match t.value,s.value with
      | some t',some s'=>some (⟨some t',[s'],ub.2⟩:Call)
      | _,_=>none).toList++r.value,t.work+s.work+r.work+12⟩
@[simp] theorem ordinaryQueriesMeter_value (T S : Tree) (qs : List (List Nat×Nat)) :
 (ordinaryQueriesMeter T S qs).value=liftQueries T S qs:=by
 induction qs with
 | nil=>rfl
 | cons ub qs ih=>
   simp only [ordinaryQueriesMeter,liftQueries,List.filterMap_cons,meterRestrict_value]
   cases ht:restrict ub.1 T <;> cases hs:restrict ub.1 S <;> simp [ih,liftQueries]

def answerFlattenMeter : List (Nat×List (List Nat))→Charged (List (List Nat))
 | []=>⟨[],2⟩
 | x::xs=>let r:=answerFlattenMeter xs
   ⟨x.2++r.value,2*x.2.length+r.work+12⟩
@[simp] theorem answerFlattenMeter_value (xs : List (Nat×List (List Nat))) :
 (answerFlattenMeter xs).value=xs.flatMap Prod.snd:=by
 induction xs <;> simp_all [answerFlattenMeter]
def optionFlattenMeter (o : Option (List (Nat×List (List Nat)))) : Charged (Option (List (List Nat))):=
 match o with
 | none=>⟨none,2⟩
 | some xs=>let f:=answerFlattenMeter xs;⟨some f.value,f.work+4⟩
@[simp] theorem optionFlattenMeter_value (o : Option (List (Nat×List (List Nat)))) :
 (optionFlattenMeter o).value=o.map (fun xs=>xs.flatMap Prod.snd):=by
 cases o <;> simp [optionFlattenMeter]

def ordinaryLocalSource (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (Q : List (List Nat)) (b : Nat) : SourceExecution:=
 let prep:=ordinaryPrepareMeter T S Q
 match prep.value with
 | none=>⟨⟨none,[]⟩,prep.work+4⟩
 | some js=>let r:=scheduleSourceMeter (mafRecursiveMeter actual T S) b js
   let f:=optionFlattenMeter r.value.answers
   let qs:=ordinaryQueriesMeter T S r.queries
   ⟨⟨f.value,qs.value⟩,prep.work+r.callerWork+r.recursiveWork+f.work+qs.work+16⟩

@[simp] theorem ordinaryLocalSource_value (actual : GenericForest.FrontierWork.Ordinary)
 (T S : Tree) (Q : List (List Nat)) (b : Nat) :
 (ordinaryLocalSource actual T S Q b).value=ordinaryExecution (GenericForest.solve actual) T S Q b:=by
 simp only [ordinaryLocalSource,ordinaryExecution,ordinaryPrepareMeter_value]
 cases h:MafScheduler.prepare T S Q with
 | none=>rfl
 | some js=>
   simp only [optionFlattenMeter_value,scheduleSourceMeter_value,ordinaryQueriesMeter_value,
    scheduleSourceMeter_queries,mafRecursiveMeter_value,PaidQueries.meterSchedule_value,liftQueries]
   rfl

def ordinarySource (actual : GenericForest.FrontierWork.Ordinary) (W : Tree→Tree→Nat→Nat)
 (T S : Tree) (Q : List (List Nat)) (b : Nat) : SourceExecution:=
 let l:=ordinaryLocalSource actual T S Q b
 ⟨l.value,l.work+callsForestDebit actual W l.value.calls⟩
@[simp] theorem ordinarySource_value (actual : GenericForest.FrontierWork.Ordinary)
 (W : Tree→Tree→Nat→Nat) (T S : Tree) (Q : List (List Nat)) (b : Nat) :
 (ordinarySource actual W T S Q b).value=ordinaryExecution (GenericForest.solve actual) T S Q b:=by
 exact ordinaryLocalSource_value actual T S Q b
theorem ordinarySource_split (actual : GenericForest.FrontierWork.Ordinary)
 (W : Tree→Tree→Nat→Nat) (T S : Tree) (Q : List (List Nat)) (b : Nat) :
 (ordinarySource actual W T S Q b).work=
 (ordinarySource actual (fun _ _ _=>0) T S Q b).work+
 GenericForest.FrontierWork.queryWork W
  (OrdinaryDispatch.WorkIntegration.forestQueries actual (ordinaryExecution (GenericForest.solve actual) T S Q b).calls):=by
 have split:=callsForestDebit_split actual W (ordinaryLocalSource actual T S Q b).value.calls
 simp only [ordinaryLocalSource_value] at split
 simp only [ordinarySource,ordinaryLocalSource_value]
 omega
end OrdinaryDispatch.Hard2SourceWork
