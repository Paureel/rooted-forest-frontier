import OriginalPaid
import MafPrecontrols

namespace Universal233.MafScheduler.ConsumerControls
open RMAF PaidQueries Precontrols

def testT : Tree := .node (cross 0) (cross 4)
def testS : Tree := .node (four 0) (four 4)
def testQ : Forest := [group 0,group 4]
def testt (U : List Nat) : Tree := if U=group 0 then cross 0 else cross 4
def tests (U : List Nat) : Tree := if U=group 0 then four 0 else four 4

theorem fixture_minimum (i : Nat)
    (hreject : DepthOne.pretest01 (cross i) (four i)=.rejected)
    (hvalid : agreement (cross i) (four i) (three i)=true) :
    LocalMinimum (cross i) (four i) 2 := by
  exact ⟨⟨three i,hvalid,rfl⟩,DepthOne.rejected_lower_bound _ _ hreject⟩

theorem test_local_min : ∀ U∈testQ, LocalMinimum (testt U) (tests U) 2 := by
  intro U hU
  have he : U=group 0 ∨ U=group 4 := by simpa [testQ] using hU
  rcases he with rfl | rfl
  · simp only [testt,tests,ite_true]
    exact fixture_minimum 0 (by decide) (by decide)
  · have hn : group 4≠group 0 := by decide
    simp only [testt,tests,hn,ite_false]
    exact fixture_minimum 4 (by decide) (by decide)

theorem test_restrictions :
    (∀ U∈testQ, restrict U testT=some (testt U)) ∧
    (∀ U∈testQ, restrict U testS=some (tests U)) := by
  constructor <;> intro U hU
  all_goals
    have he : U=group 0 ∨ U=group 4 := by simpa [testQ] using hU
    rcases he with rfl | rfl <;> decide

theorem table_return_sound (t s : Tree) (b : Nat) (F : Forest)
    (h : table t s b=some F) : agreement t s F=true ∧ F.length-1=2 ∧ 2≤b := by
  unfold table at h
  dsimp only at h
  split at h
  · rename_i hc
    have he : three (leaves s).head!=F := by simpa using h
    rw [←he]
    have hh : agreement t s (three (leaves s).head!)=true ∧
        (three (leaves s).head!).length-1≤b := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using hc
    exact ⟨hh.1,rfl,by simpa [three] using hh.2⟩
  · simp at h

theorem control_actual_sound_consumer :
    agreement testT testS (three 0++three 4)=true ∧
      RestrictionBridge.Refines (three 0++three 4) testQ ∧
      (three 0++three 4).length-testQ.length=(testQ.map (fun _ => 2)).sum ∧
      (three 0++three 4).length-testQ.length≤4 := by
  apply disjoint_caller_sound testT testS testQ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) testt tests (fun _ => 2)
    test_restrictions.1 test_restrictions.2 test_local_min table
    (fun U _ b F hF => table_return_sound (testt U) (tests U) b F hF) 4
    (three 0++three 4)
  decide

theorem control_actual_paid_consumer (c : Rat) (hc : 2≤c) (q : Nat) :
    actualQueryMass c q (calls testT testS table q testQ)≤c^(-1 : Int) := by
  exact disjoint_actual_paid_mass testT testS testQ (by decide) (by decide)
    (by decide) (by decide) testt tests (fun _ => 2) test_restrictions.1 test_restrictions.2
    test_local_min table q (by decide) c hc
end Universal233.MafScheduler.ConsumerControls
