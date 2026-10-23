import LocalDispatchBounds
namespace OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence Universal233.BothBad
open OrdinaryDispatch.FullSourceWork Universal233.Rule5SelectedLocalWork

def executionPolynomial (N : Nat) := dispatchPolynomial N+
 agreementK (payloadSize N)+payloadSize N+4*N+30

theorem checked_payload_bound (T S : Tree) (q N : Nat) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (answer : Option (List (List Nat)))
 (caps:∀F,answer=some F→F.length≤payloadSize N ∧ F.flatten.length≤payloadSize N) :
 (checkedMeter T S q answer).work≤agreementK (payloadSize N)+payloadSize N+6 := by
 have grow:N≤payloadSize N:=by unfold payloadSize;omega
 cases answer with
 | none=>simp [checkedMeter]
 | some F=>
   have p:=caps F rfl
   have check:=measuredAgreement_K T S (payloadSize N) (by omega) (by omega) F
     (by unfold Rule5LocalWork.cells;omega)
   change (agreementMeter T S F).work≤agreementK (payloadSize N) at check
   simp only [checkedMeter];omega

theorem execution_size (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (q N : Nat) (es : List Entry) (tn:treeNodes T≤N) :
 ∀F,(bothBadExecuteLocalSource actual T S q es).value.answer=some F→F.length≤N := by
 intro F h
 rw [bothBadExecuteLocalSource_value] at h
 have a:=(execute_sound (GenericForest.solve actual) T S q es F h).1
 have p:partitionCheck (leaves T) F=true:=by simp only [agreement,Bool.and_eq_true] at a;exact a.1.1.1.1
 exact Nat.le_trans (SourceCoverage.partitionCheck_block_bound _ _ p) (Nat.le_trans (leaves_nodes T) tn)

/-- Exact recursive execution sum. No list occurrence is discarded: failed,
 unaffordable-output-filter survivors and duplicate entries all pay locally. -/
theorem execute_bound (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
 (q N : Nat) (es : List Entry) (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (caps:∀e,e∈es→EntryCap N e) :
 (bothBadExecuteLocalSource actual T S q es).work≤executionPolynomial N*es.length+2 ∧
 (bothBadExecuteLocalSource actual T S q es).value.calls.length≤N*es.length := by
 induction es with
 | nil=>simp [bothBadExecuteLocalSource]
 | cons e es ih=>
   have tail:=ih (by intro x h;exact caps x (by simp [h]))
   have cur:=dispatch_bound actual T S e N three tn sn (caps e (by simp))
   have raw:=dispatch_payload actual T S e N three tn sn (caps e (by simp))
   have check:=checked_payload_bound T S q N tn sn _ raw
   have choose:=chooseMeter_bound
    (checkedMeter T S q (bothBadDispatchLocalSource actual T S e).value.answer).value
    (bothBadExecuteLocalSource actual T S q es).value.answer N
    (checkedMeter_size T S q _ N (Nat.le_trans (leaves_nodes T) tn))
    (execution_size actual T S q N es tn)
   simp only [bothBadExecuteLocalSource,List.length_append,List.length_cons,Nat.mul_add,Nat.mul_one]
   simp only [executionPolynomial] at *
   exact ⟨by omega,by omega⟩

theorem actual_plan_execute_bound (actual : GenericForest.FrontierWork.Ordinary) (S T : Tree)
 (A B C D : List Nat) (q N : Nat) (three:3≤N) (tn:treeNodes T≤N) (sn:treeNodes S≤N)
 (al:A.length≤N) (bl:B.length≤N) (cl:C.length≤N) :
 (bothBadExecuteLocalSource actual T S q (bothBadPlanMeter S T A B C D q).value).work≤
   executionPolynomial N*(bothBadPlanMeter S T A B C D q).value.length+2 :=
 (execute_bound actual T S q N _ three tn sn (plan_cap S T A B C D q N sn al bl cl)).1
end OrdinaryDispatch.Hard2SourceWork.LocalDispatchEnvelope
