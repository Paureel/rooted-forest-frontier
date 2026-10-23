import PaidForestPretestWork
import SelectedAgreementBinding
namespace Universal233.Rule5ExecutionSource
open RMAF ForestState CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion
open WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork

structure CurrentReceipt where
 value : Rule5PaidOrdinary.CurrentResult
 prefixWork : Nat
 forestDebit : Nat
 ordinaryCalls : List Query
 deriving Repr

/-- The forest debit is the completed implemented source counter, with the
same callback and current state. It is not a fee for this execution spine. -/
def currentQueryMeter (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) : CurrentReceipt :=
 let p:=forestPretestMeter T ss
 match p.value with
 | .refused=>⟨.malformed,p.work+2,0,[]⟩
 | .found F=>⟨.answered (if additionalCost ss F≤r then some F else none),p.work+F.length+ss.length+4,0,[]⟩
 | .rejected=>if r≤1 then ⟨.answered none,p.work+3,0,[]⟩ else
    ⟨.answered (GenericForest.solve cb T ss r),p.work+3,forestWork cb W T ss r,frontier cb T ss r⟩

theorem current_query_value (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentQueryMeter cb W T ss r).value=Rule5PaidOrdinary.currentQuery cb T ss r := by
 simp only [currentQueryMeter,forest_pretest_value,Rule5PaidOrdinary.currentQuery]
 split <;> first | rfl | split <;> rfl

def currentAnswerSource (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) : Charged (Option Forest) :=
 let x:=currentQueryMeter cb W T ss r
 ⟨x.value.answer?,x.prefixWork+x.forestDebit+1⟩

theorem current_answer_value (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentAnswerSource cb W T ss r).value=Rule5PaidOrdinary.currentAnswer cb T ss r := by
 simp only [currentAnswerSource,current_query_value,Rule5PaidOrdinary.currentAnswer]

theorem current_prefix_zero (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentQueryMeter cb W T ss r).prefixWork=(currentQueryMeter cb (fun _ _ _=>0) T ss r).prefixWork := by
 simp only [currentQueryMeter];split <;> first | rfl | split <;> rfl

theorem current_calls_zero (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentQueryMeter cb W T ss r).ordinaryCalls=(currentQueryMeter cb (fun _ _ _=>0) T ss r).ordinaryCalls := by
 simp only [currentQueryMeter];split <;> first | rfl | split <;> rfl

theorem current_forest_split (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentQueryMeter cb W T ss r).forestDebit=(currentQueryMeter cb (fun _ _ _=>0) T ss r).forestDebit+
 queryWork W (currentQueryMeter cb W T ss r).ordinaryCalls := by
 simp only [currentQueryMeter]
 split <;> first | simp [queryWork] | split <;> first | simp [queryWork] | exact forestWork_split cb W T ss r

theorem current_answer_split (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat) :
 (currentAnswerSource cb W T ss r).work=(currentAnswerSource cb (fun _ _ _=>0) T ss r).work+
 queryWork W (currentQueryMeter cb W T ss r).ordinaryCalls := by
 simp only [currentAnswerSource,current_prefix_zero,current_forest_split]
 omega

def currentPrefixBudget (N : Nat) := forestPretestBudget N+2*N+6

theorem current_prefix_work (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r N : Nat)
 (tn : targetNodes T≤N) (sn : sourceNodes ss≤N) :
 (currentQueryMeter cb W T ss r).prefixWork≤currentPrefixBudget N := by
 have pre:=forest_pretest_work T ss N tn sn
 have sl:=Nat.le_trans (source_count_nodes ss) sn
 simp only [currentQueryMeter]
 split
 · dsimp only;unfold currentPrefixBudget;omega
 · rename_i F hF
   have hn : ForestPretest01.pretest01 T ss=.found F:=by rw [←forest_pretest_value];exact hF
   have mem:=(ForestPretest01.found_spec T ss F hn).2.1
   have size:=forest_candidates_payload ss (by simpa only [forest_candidates_value] using mem)
   dsimp only;unfold currentPrefixBudget;omega
 · split <;> dsimp only <;> unfold currentPrefixBudget <;> omega

/-- Only the literal rejected, residual>1 branch enters GenericForest.solve. -/
theorem current_fallback_gate (cb : Ordinary) (W : OrdinaryWork) (T : Option Tree) (ss : List Tree) (r : Nat)
 (gate : ¬(ForestPretest01.pretest01 T ss=.rejected ∧ 1<r)) :
 (currentQueryMeter cb W T ss r).forestDebit=0 ∧ (currentQueryMeter cb W T ss r).ordinaryCalls=[] := by
 simp only [currentQueryMeter,forest_pretest_value]
 split
 · exact ⟨rfl,rfl⟩
 · exact ⟨rfl,rfl⟩
 · rename_i rejected
   have small : r≤1:=by omega
   simp only [small,ite_true];exact ⟨rfl,rfl⟩
end Universal233.Rule5ExecutionSource
