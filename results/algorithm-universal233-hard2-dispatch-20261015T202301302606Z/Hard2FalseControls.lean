import Hard2Controls
open RMAF Universal233 OrdinaryDispatch.Hard2Dispatcher OrdinaryDispatch.Hard2Dispatcher.Controls
example : (run refusal T S c d 1).isSome=true := by cbv
example : (run refusal T S c d 2).any (fun F=>decide (F.length=2))=true := by cbv
example : ((paidCase OrdinaryDispatch.GoodPairDP.Controls.depthAnswer OrdinaryDispatch.GoodPairDP.Controls.target (OrdinaryDispatch.GoodPairDP.Controls.source OrdinaryDispatch.GoodPairDP.Controls.badC) PairRoute.raw 4 (.pair .abc (.edge PairRoute.edge))).calls.map BothBad.Call.budget)=[2] := by cbv
example : Rule5Local.admitted Rule5Local.Pre.commonT Rule5Local.Pre.commonS ActualFirst.c.a ActualFirst.c.b=true := by cbv
