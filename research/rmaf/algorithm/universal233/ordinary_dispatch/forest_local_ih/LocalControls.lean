import ForestDisjoint
import ForestProgramControls
namespace GenericForest.LocalIH.Controls
open RMAF ForestState GenericForest.Controls Universal233.PaidQueries

def cutoff (t s : Tree) (q : Nat) : Option Forest :=
  if q ≤ 2 then table t s q else none

-- Declared before the bounded-congruence construction. This exercises an
-- actual paid hard callback and a separate actual overlap recursion.
theorem paid_fixture :
    solve cutoff (some (.node (four 0) (cross 4))) [four 0,four 4] 2 =
      some [[0,1,2,3],[4],[5],[6,7]] ∧
    solve cutoff (some (four 0)) ss 1 = some [[0],[2],[1,3]] := by cbv

theorem paid_budget_fixture :
    (disjointAttempt (.node (four 0) (cross 4)) [four 0,four 4] cutoff 2).map
      Receipt.calls = some [2] := by decide

theorem out_of_budget_difference :
    table (cross 4) (four 4) 3 ≠ cutoff (cross 4) (four 4) 3 := by decide

theorem scheduler_budget : allocated 4
    ([.resolved 0 1 (), .hard 1, .hard 2] : List (Job Nat Unit)) = 1 := by decide
end GenericForest.LocalIH.Controls
