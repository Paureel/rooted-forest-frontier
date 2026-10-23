import PrefixWorkControls
open Universal233.Rule5PrefixLocalWork RMAF
example : (properPairMeter repeated repeated).value=true := by decide
example : (containsMeter 9 [0,1,2]).work=0 := by decide
example : (nodupMeter [0,1,2]).work≤3 := by decide
example : (3:Nat)+2≤3 := by decide
