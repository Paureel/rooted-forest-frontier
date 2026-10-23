import Caller

namespace Universal233.PaidQueries.Precontrols

def plantedSolver (opt b : Nat) : Option (Nat × Nat) := if opt ≤ b then some (opt,opt) else none
def k (n : Nat) : Job Nat Nat := .resolved n n n
def h (n : Nat) : Job Nat Nat := .hard n

-- The expected entries are the manually pinned independent truth table.
theorem control_resolved : (schedule plantedSolver 1 [k 0,k 1]).answers = some [(0,0),(1,1)] ∧
    (schedule plantedSolver 1 [k 0,k 1]).calls = [] := by decide
theorem control_other_good_cost : (schedule plantedSolver 3 [k 1,h 2]).calls = [2] ∧
    (schedule plantedSolver 3 [k 1,h 2]).answers = some [(1,1),(2,2)] := by decide
theorem control_two_hard : (schedule plantedSolver 4 [h 2,h 2]).calls = [2,2] ∧
    (schedule plantedSolver 4 [h 2,h 2]).answers = some [(2,2),(2,2)] := by decide
theorem control_sum_reject : (schedule plantedSolver 5 [h 3,h 3]).calls = [3,3] ∧
    (schedule plantedSolver 5 [h 3,h 3]).answers = none := by decide
theorem control_query_failure : (schedule plantedSolver 6 [h 2,h 6]).calls = [4,4] ∧
    (schedule plantedSolver 6 [h 2,h 6]).answers = none := by decide
theorem control_early_prune : (schedule plantedSolver 3 [h 2,h 2]).calls = [] ∧
    (schedule plantedSolver 3 [h 2,h 2]).visits = 0 := by decide
theorem control_sole_hard : (schedule plantedSolver 3 [h 2]).calls = [3] ∧
    (schedule plantedSolver 3 [h 2]).answers = some [(2,2)] := by decide
theorem control_empty : (schedule plantedSolver 0 ([] : List (Job Nat Nat))).answers = some [] ∧
    (schedule plantedSolver 0 ([] : List (Job Nat Nat))).calls = [] := by decide
theorem control_known_overbudget : (schedule plantedSolver 0 [k 1]).calls = [] ∧
    (schedule plantedSolver 0 [k 1]).answers = none := by decide
theorem control_three_hard : (schedule plantedSolver 6 [h 2,h 2,h 2]).calls = [2,2,2] ∧
    (schedule plantedSolver 6 [h 2,h 2,h 2]).answers = some [(2,2),(2,2),(2,2)] := by decide
end Universal233.PaidQueries.Precontrols
