import LiteralControls
open Universal233.BinaryCheap.Controls
open Universal233 RMAF CoreProgram
-- The source-P guard must reject the overlap-only target.
theorem false_source : pairwiseEmbeddings t [a,b,c] = true := by decide
-- A bad parent does not make both cheap sectors bad.
theorem false_sector : restrictionAgrees s t [1,2] = false := by decide
-- Original F is not necessarily a proof-exchanged output witness.
theorem false_refinement : ((generate oldS oldColor 6).outputs.any (fun o => refinesBool oldF o.partition)) = true := by decide
