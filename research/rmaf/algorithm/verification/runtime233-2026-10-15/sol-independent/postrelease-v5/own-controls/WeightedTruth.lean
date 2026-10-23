import PrefixSourceWork
open RMAF Universal233 OrdinaryDispatch.FullSourceWork
example : budgetTreeWork 0 (.leaf 0) (.leaf 1)=1 := by rw [budgetTreeWork_eq]; decide +kernel
example : budgetTreeWork 1 (.leaf 0) (.leaf 1)=(233/100:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
example : budgetTreeWork 2 (.leaf 0) (.leaf 1)=(54289/10000:Rat) := by rw [budgetTreeWork_eq]; decide +kernel
example : prefixCoefficient 0=2097152 := by decide +kernel
example : prefixCoefficient 1=1528823808 := by decide +kernel
example : prefixTreeWork 0 (.leaf 0) (.leaf 1)=prefixTreeWork 1000 (.leaf 0) (.leaf 1) := by rw [prefixTreeWork_eq,prefixTreeWork_eq]; decide +kernel
example : ([1,0,1].map (fun r=>Rule5ActualTrace.base^r)).sum=(283/50:Rat) := by decide +kernel
