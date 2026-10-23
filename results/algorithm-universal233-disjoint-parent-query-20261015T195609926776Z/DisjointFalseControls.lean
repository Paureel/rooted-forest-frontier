import DisjointControls
open RMAF Universal233 Universal233.BothBad OrdinaryDispatch.DisjointParents OrdinaryDispatch.DisjointParents.Controls
example : ((query noAnswer hardT hardS hardP 6).calls.map Call.budget)=[4] := by cbv
example : (query noAnswer smallT smallS smallP 4).answer.any (fun F=>decide (F.length-1=2))=true := by cbv
example : (query noAnswer hardT hardS hardP 1).answer.isSome=true := by cbv
