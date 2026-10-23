import Precontrols
open Universal233.PaidQueries Universal233.PaidQueries.Precontrols
-- Mutant omitting final sum would accept both successful opt3 calls at q5.
example : (schedule plantedSolver 5 [h 3,h 3]).answers.isSome = true := by decide
-- Mutant charging its own hard minimum would allocate1, rather than3.
example : (schedule plantedSolver 3 [h 2]).calls = [1] := by decide
-- Mutant subtracting ALL hard lower bounds would allocate0, rather than2.
example : (schedule plantedSolver 4 [h 2,h 2]).calls = [0,0] := by decide
-- Mutant pruning at3 per hard would reject the feasible two opt2 jobs.
example : (schedule plantedSolver 4 [h 2,h 2]).answers = none := by decide
