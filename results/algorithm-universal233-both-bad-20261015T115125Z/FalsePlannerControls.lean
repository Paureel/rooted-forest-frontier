import PlannerControls
open Universal233.BothBad Universal233.BothBad.Precontrols
example : chargedCosts (plan S T A B C D 5)=[3,4,4] := by decide
example : budgets (plan S T A B C D 4)=[1,0,0] := by decide
example : chargedCosts (plan S T A B C D 2)=[3] := by decide
