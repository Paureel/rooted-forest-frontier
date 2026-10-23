import WeightedOrdinaryWork
open RMAF OrdinaryDispatch.FullSourceWork
example : budgetTreeWork 1 (.leaf 0) (.leaf 1)=(1:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
