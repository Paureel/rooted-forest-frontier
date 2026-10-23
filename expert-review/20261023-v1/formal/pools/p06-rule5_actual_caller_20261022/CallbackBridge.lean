import AnswerBridge
import ControlFlowV4

namespace ActualRule5Caller
open RMAF Universal233 ForestState ForestMinCompletion OrdinaryDispatch
open Universal233.Rule5PaidOrdinary IndependentReconstruction

/-- The source-identical original cutoff callback has full local ordinary
correctness at every strictly smaller request residual. -/
theorem original_below_local (q : Nat) (below : BelowBudget q) :
    BelowIH q (OwnPaid q) := by
  intro r hr
  constructor
  · intro t s b F hb proper found
    have bq : b < q := Nat.lt_of_le_of_lt hb hr
    have hf : FastOrdinary.solve b t s = some F := by
      simpa [OwnPaid,bq] using found
    have ex := below b bq t s proper
    simpa only [hf,QueryExact] using ex
  · intro t s b G hb proper hG bound
    have bq : b < q := Nat.lt_of_le_of_lt hb hr
    have ex := below b bq t s proper
    cases found : FastOrdinary.solve b t s with
    | none =>
      have impossible : b < G.length - 1 := by
        exact (show ∀ H, agreement t s H = true → b < H.length - 1 from
          by simpa only [found,QueryExact] using ex) G hG
      omega
    | some F =>
      exact ⟨F,by simp [OwnPaid,bq,found]⟩

#print axioms original_below_local
end ActualRule5Caller
