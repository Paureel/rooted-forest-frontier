import PaidPlanSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork Rule5SelectedLocalWork Case322Extraction Case322PaidGuard Rule5PaidSelector

def requestForMeter (T S : Tree) (q : Nat) (c : Branch) : Charged (Option PaidRequest) :=
 if c.originalCuts.length≤q then
  let s:=sourceForestMeter (current T S c) c.partition
  ⟨some ⟨c,opposite T S c,s.value,q-c.originalCuts.length⟩,s.work+2*c.originalCuts.length+7⟩
 else ⟨none,c.originalCuts.length+2⟩
@[simp] theorem request_for_value (T S : Tree) (q : Nat) (c : Branch) :
 (requestForMeter T S q c).value=requestFor T S q c := by
 simp only [requestForMeter,requestFor,paid,source_forest_value,Rule5Case322.sourceForest,OutputState.sourceForest]
 split <;> rfl

/-- Strict filterMap: every retained branch is attempted in source order,
including duplicate branches and failed requests. -/
def requestListMeter (T S : Tree) (q : Nat) : List Branch→Charged (List PaidRequest)
 | []=>⟨[],1⟩
 | c::cs=>let a:=requestForMeter T S q c;let r:=requestListMeter T S q cs
           ⟨match a.value with | none=>r.value | some j=>j::r.value,a.work+r.work+3⟩
@[simp] theorem request_list_value (T S : Tree) (q : Nat) (cs : List Branch) :
 (requestListMeter T S q cs).value=cs.filterMap (requestFor T S q) := by
 induction cs <;> simp_all only [requestListMeter,request_for_value,List.filterMap_cons,List.filterMap_nil] <;> rfl

/-- Includes the literal builder, currentGuard filter and affordable request
materializers, rather than replacing guardedPlan by its proof-level equality. -/
def requestsMeter {T S : Tree} (D : LiteralGeometry T S) (q : Nat) : Charged (List PaidRequest) :=
 let p:=literalPlanMeter D;let g:=guardedPlanMeter D p;let r:=requestListMeter T S q g.value
 ⟨r.value,g.work+r.work+2⟩
@[simp] theorem requests_value {T S : Tree} (D : LiteralGeometry T S) (q : Nat) :
 (requestsMeter D q).value=requests D q := by
 simp only [requestsMeter,request_list_value,guarded_plan_value D _ (literal_plan_value D),requests]

/-- Rejected pretest and r>1 are the only native forest execution boundary. -/
structure PaidExecutionReceipt (α : Type) where
 value : α
 prefixWork : Nat
 forestDebit : Nat
 ordinaryCalls : List GenericForest.FrontierWork.Query
 deriving Repr

def requestAnswerMeter (cb : Ordinary) (W : OrdinaryWork) (j : PaidRequest) : PaidExecutionReceipt (Option Forest) :=
 let a:=currentQueryMeter cb W (some j.target) j.sources j.residual
 ⟨a.value.answer?,a.prefixWork+1,a.forestDebit,a.ordinaryCalls⟩
@[simp] theorem request_answer_value (cb : Ordinary) (W : OrdinaryWork) (j : PaidRequest) :
 (requestAnswerMeter cb W j).value=Rule5PaidOrdinary.currentAnswer cb (some j.target) j.sources j.residual := by
 simp only [requestAnswerMeter,current_query_value,Rule5PaidOrdinary.currentAnswer]

def answerListMeter (cb : Ordinary) (W : OrdinaryWork) : List PaidRequest→PaidExecutionReceipt (List Forest)
 | []=>⟨[],1,0,[]⟩
 | j::js=>let a:=requestAnswerMeter cb W j;let r:=answerListMeter cb W js
           ⟨match a.value with | none=>r.value | some F=>F::r.value,
             a.prefixWork+r.prefixWork+3,a.forestDebit+r.forestDebit,a.ordinaryCalls++r.ordinaryCalls⟩
@[simp] theorem answer_list_value (cb : Ordinary) (W : OrdinaryWork) (js : List PaidRequest) :
 (answerListMeter cb W js).value=js.filterMap (fun j=>Rule5PaidOrdinary.currentAnswer cb (some j.target) j.sources j.residual) := by
 induction js <;> simp_all only [answerListMeter,request_answer_value,List.filterMap_cons,List.filterMap_nil] <;> rfl

def answersMeter (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) : PaidExecutionReceipt (List Forest) :=
 let js:=requestsMeter R.geometry q;let a:=answerListMeter cb W js.value
 ⟨a.value,js.work+a.prefixWork+2,a.forestDebit,a.ordinaryCalls⟩
@[simp] theorem answers_value (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (answersMeter cb W R q).value=Rule5PaidOrdinary.answers cb R q := by
 simp only [answersMeter,answer_list_value,requests_value,Rule5PaidOrdinary.answers]
end Universal233.Rule5ExecutionSource
