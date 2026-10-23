import ForestProgram
namespace ForestMinCompletion.Controls
open RMAF
theorem nat_least_control : (3 = 3 ∨ 3 = 5) ∧ ∀ n : Nat, n = 3 ∨ n = 5 → 3 ≤ n := by
 constructor
 · exact Or.inl rfl
 · intro n h; rcases h with h | h <;> omega
def single : Tree := .leaf 0
def cherry : Tree := .node (.leaf 0) (.leaf 1)
def improper : Tree := .node (.leaf 0) (.leaf 0)
theorem single_agrees : agreement single single [[0]] = true := by decide
theorem single_cost : ([[0]] : List (List Nat)).length-1 = 0 := by decide
theorem cherry_split_agrees : agreement cherry cherry [[0],[1]] = true := by decide
theorem cherry_join_agrees : agreement cherry cherry [[0,1]] = true := by decide
theorem cherry_costs : ([[0],[1]] : List (List Nat)).length-1 = 1 ∧
 ([[0,1]] : List (List Nat)).length-1 = 0 := by decide
theorem improper_rejected : Universal233.DepthOne.proper improper improper = false := by decide
end ForestMinCompletion.Controls
