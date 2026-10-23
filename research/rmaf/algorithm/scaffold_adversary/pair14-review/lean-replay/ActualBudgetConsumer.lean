import PairWitness
open Universal233.CoreProgram Universal233.ScaffoldWitness

-- Initial graph review budget12 minus the two actual pendant cuts leaves10.
theorem actual_remaining_budget_A :
    (generate sourceA aColor 10).outputs = actualA.outputs := by decide
theorem actual_remaining_budget_A_swap :
    (generate sourceA (fun x => 1 - aColor x) 10).outputs = actualA.outputs := by decide
theorem actual_remaining_budget_B :
    (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 0 else 1) 10).outputs =
    (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 0 else 1) 1).outputs := by decide
theorem actual_remaining_budget_B_swap :
    (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 1 else 0) 10).outputs =
    (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 0 else 1) 1).outputs := by decide

#print axioms actual_remaining_budget_A
#print axioms actual_remaining_budget_A_swap
#print axioms actual_remaining_budget_B
#print axioms actual_remaining_budget_B_swap
