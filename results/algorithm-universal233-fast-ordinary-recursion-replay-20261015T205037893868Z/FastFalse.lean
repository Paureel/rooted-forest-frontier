import FastControls
open OrdinaryDispatch.FastOrdinary OrdinaryDispatch.FastOrdinary.Controls
open RMAF ForestState OrdinaryDispatch Universal233 Universal233.CherryBranching
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
-- Each deliberately false source/budget/priority claim must reject.
example : cutoff (fun _ _ _ => some [[0]]) 3 (.leaf 0) (.leaf 0) 3=some [[0]] := by decide
example : etag (early oneS oneT)=9 := by decide
example : (leaves (contract 4 5 (commonFresh graftS) graftS)).length=(leaves graftT).length := by decide
example : (external quartetT quartetS 2).isSome=true := by
 rw [external_ktwo]
 decide
