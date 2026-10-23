import CallerControls
open RMAF OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Caller.Controls
example : replyCost (pickMerge OrdinaryCommonSplit.Controls.T OrdinaryCommonSplit.Controls.S
    OrdinaryCommonSplit.Controls.X OrdinaryCommonSplit.Controls.Y 0 3 6 7 FM FN)=some 1 := by decide
example : (mergeCandidates OrdinaryCommonSplit.Controls.X OrdinaryCommonSplit.Controls.Y
    0 3 6 7 FMrev FNrev).all (agreement OrdinaryCommonSplit.Controls.T OrdinaryCommonSplit.Controls.S)=true := by decide
