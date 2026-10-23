import BOControls
open OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.BudgetOptimization.Controls
-- Four deliberately false propositions; each must fail at its control site.
example : trialWork (fun q => 2^q) (scan synthetic 0 3).trials≤2 := by decide +kernel
-- Corrupted singleton cut/component conversion: 0 cuts = 1 component.
example : (0:Nat)=1 := by decide +kernel
example : (scan synthetic 0 3).trials=[(1,some [[0]])] := by decide +kernel
example : (2:Nat)+3=6 := by decide +kernel
