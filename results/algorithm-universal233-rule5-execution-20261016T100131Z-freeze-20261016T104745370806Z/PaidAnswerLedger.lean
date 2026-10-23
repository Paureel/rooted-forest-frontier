import PaidPlanWork
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard

theorem query_work_append (W : OrdinaryWork) (A B : List Query) : queryWork W (A++B)=queryWork W A+queryWork W B := by
 simp only [queryWork,List.map_append,List.sum_append]

theorem request_answer_prefix_zero (cb : Ordinary) (W : OrdinaryWork) (j : PaidRequest) :
 (requestAnswerMeter cb W j).prefixWork=(requestAnswerMeter cb (fun _ _ _=>0) j).prefixWork := by
 simp only [requestAnswerMeter,current_prefix_zero]

theorem answer_list_prefix_zero (cb : Ordinary) (W : OrdinaryWork) (js : List PaidRequest) :
 (answerListMeter cb W js).prefixWork=(answerListMeter cb (fun _ _ _=>0) js).prefixWork := by
 induction js <;> simp_all only [answerListMeter,request_answer_prefix_zero]

theorem answer_list_debit_split (cb : Ordinary) (W : OrdinaryWork) (js : List PaidRequest) :
 (answerListMeter cb W js).forestDebit=(answerListMeter cb (fun _ _ _=>0) js).forestDebit+
 queryWork W (answerListMeter cb W js).ordinaryCalls := by
 induction js with
 | nil=>simp [answerListMeter,queryWork]
 | cons j js ih=>
  have h:=current_forest_split cb W (some j.target) j.sources j.residual
  simp only [answerListMeter,requestAnswerMeter,query_work_append];omega

theorem answers_prefix_zero (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (answersMeter cb W R q).prefixWork=(answersMeter cb (fun _ _ _=>0) R q).prefixWork := by
 simp only [answersMeter,answer_list_prefix_zero]

theorem answers_debit_split (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (answersMeter cb W R q).forestDebit=(answersMeter cb (fun _ _ _=>0) R q).forestDebit+
 queryWork W (answersMeter cb W R q).ordinaryCalls := answer_list_debit_split cb W _

theorem answer_list_calls (cb : Ordinary) (W : OrdinaryWork) (js : List PaidRequest) :
 (answerListMeter cb W js).ordinaryCalls=js.flatMap (fun j=>(currentQueryMeter cb W (some j.target) j.sources j.residual).ordinaryCalls) := by
 induction js <;> simp_all [answerListMeter,requestAnswerMeter]

theorem current_calls_native (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentQueryMeter cb W T ss r).ordinaryCalls=Rule5ActualTrace.currentFrontier cb T ss r := by
 simp only [currentQueryMeter,forest_pretest_value,Rule5ActualTrace.currentFrontier]
 cases hp:ForestPretest01.pretest01 T ss <;> simp only [hp]
 all_goals first | rfl | split <;> rfl

theorem answers_calls_native (cb : Ordinary) (W : OrdinaryWork) {T S : Tree} (R : SelectedPaid T S) (q : Nat) :
 (answersMeter cb W R q).ordinaryCalls=Rule5ActualTrace.queries cb (.paidRequests (requests R.geometry q)) := by
 simp only [answersMeter,answer_list_calls,requests_value,current_calls_native,Rule5ActualTrace.queries]
end Universal233.Rule5ExecutionSource
