import LocalExact
import LocalControls
namespace GenericForest.LocalIH.Controls
open RMAF ForestState GenericForest.Controls Universal233.PaidQueries

def tooSmall (t s : Tree) (q : Nat) : Option Forest :=
  if q ≤ 1 then table t s q else none

theorem bound_is_essential :
    solve tooSmall (some (.node (four 0) (cross 4))) [four 0,four 4] 2 = none ∧
    solve table (some (.node (four 0) (cross 4))) [four 0,four 4] 2 =
      some [[0,1,2,3],[4],[5],[6,7]] := by cbv

-- The actual p=1, known-cost=0 case pays no extra scheduler discount.
theorem singleton_hard_no_discount :
    allocated 2 ([.hard 0] : List (Job Nat Unit)) = 2 := by decide

theorem abstract_actual_consumer (actual : Tree → Tree → Nat → Option Forest)
    (q : Nat) (ih : ForestMinCompletion.LocalOrdinaryIH q actual)
    (T : Option Tree) (ss : List Tree) (G : Forest)
    (ha : agrees T ss G = true) (budget : additionalCost ss G ≤ q) :
    ∃ F, solve actual T ss q = some F ∧ F.length ≤ G.length :=
  exact_at_current_budget actual q ih T ss G ha budget
end GenericForest.LocalIH.Controls
