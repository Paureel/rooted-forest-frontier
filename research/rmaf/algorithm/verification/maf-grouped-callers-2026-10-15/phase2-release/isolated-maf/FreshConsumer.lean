import FreshReadout
import MafConsumerControls
namespace NonauthorOriginalConsumer
open RMAF Universal233 PaidQueries MafScheduler
open MafScheduler.ConsumerControls

/-- The actual original caller's q is additional to Q, not its initial cut
charge. Recursive attained-minimum soundness stays an explicit hypothesis. -/
theorem additional_and_initial_charge
    (solve : Tree → Tree → Nat → Option Forest)
    (IH : ∀ U∈testQ, ∀ b F, solve (testt U) (tests U) b=some F →
      agreement (testt U) (tests U) F=true ∧ F.length-1=2 ∧ 2≤b)
    (q : Nat) (F : Forest) (hret : solveDisjoint testT testS solve q testQ=some F) :
    agreement testT testS F=true ∧ F.length-testQ.length=4 ∧ F.length-1=5 ∧ 4≤q := by
  have h := disjoint_caller_sound testT testS testQ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) testt tests (fun _ => 2)
    test_restrictions.1 test_restrictions.2 test_local_min solve IH q F hret
  have cost : F.length-testQ.length=4 := by simpa [testQ] using h.2.2.1
  have lenQ : testQ.length=2 := rfl
  exact ⟨h.1,cost,by omega,by have := h.2.2.2; omega⟩

/-- Paid mass counts actual original bad restrictions and actual executed calls;
no recursive solver correctness or implementation is invented by this bound. -/
theorem actual_original_mass (solve : Tree → Tree → Nat → Option Forest)
    (q : Nat) (c : Rat) (hc : 2≤c) :
    actualQueryMass c q (calls testT testS solve q testQ)≤c^(-1 : Int) := by
  exact disjoint_actual_paid_mass testT testS testQ (by decide) (by decide)
    (by decide) (by decide) testt tests (fun _ => 2)
    test_restrictions.1 test_restrictions.2 test_local_min solve q (by decide) c hc

theorem literal_root_forest :
    solveDisjoint T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]=
      some [[0,1],[2],[3],[4,5],[6],[7]] ∧
    calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]=[2,2] := by decide
end NonauthorOriginalConsumer
