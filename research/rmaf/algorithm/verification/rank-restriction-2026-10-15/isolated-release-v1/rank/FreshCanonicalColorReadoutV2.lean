import Requests
import ColorClasses
import Lean
open RMAF
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
def tj : Tree → Lean.Json
  | .leaf x => Lean.Json.mkObj [("leaf",Lean.toJson x)]
  | .node l r => Lean.Json.mkObj [("node",Lean.toJson [tj l,tj r])]
def otj : Option Tree → Lean.Json
  | none => Lean.Json.null
  | some t => tj t
def emit (id : String) (j : Lean.Json) : IO Unit :=
  IO.println ("READOUT|" ++ id ++ "|" ++ j.compress)

open Universal233 Universal233.CoreProgram Universal233.SourceCoverage Universal233.RankDichotomy
def oj (o : Output) : Lean.Json := Lean.Json.mkObj [("partition",Lean.toJson o.partition),("cuts",Lean.toJson o.sourceCuts)]
def rj (r : Receipt) : Lean.Json := Lean.Json.mkObj [("outputs",Lean.toJson (r.outputs.map oj)),("refusals",Lean.toJson r.refusals),("visited",Lean.toJson r.visited),("attempts",Lean.toJson r.childAttempts),("pruned",Lean.toJson r.pruned)]
def qj (q : Rat) : Lean.Json := Lean.Json.mkObj [("num",Lean.toJson q.num),("den",Lean.toJson q.den)]

open Universal233.Assembly VertexGeometry

#eval emit "actual_one_vertex_clear/classes" (Lean.toJson ([0,1,2,3,4,5].map (fun x => [0,1,2,3,4,5].map (fun y => (localColor (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.at [])) x == (localColor (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.at [])) y))))
#eval emit "actual_one_vertex_clear/rank" (Lean.toJson (inputRank (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5))) (localColor (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.at []))))
#eval emit "actual_one_vertex_clear/receipt" (rj (generate (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5))) (localColor (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.at [])) 5))
#eval emit "actual_one_vertex_clear/internal_guard" (Lean.toJson ([!((leafList (leaves (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5)))).contains [])]))
#eval emit "actual_two_vertex_clear/classes" (Lean.toJson ([0,1,2,3,4,5,6].map (fun x => [0,1,2,3,4,5,6].map (fun y => (localColor (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6)) (.both [] [false])) x == (localColor (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6)) (.both [] [false])) y))))
#eval emit "actual_two_vertex_clear/rank" (Lean.toJson (inputRank (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5))) (.leaf 6)) (localColor (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6)) (.both [] [false]))))
#eval emit "actual_two_vertex_clear/receipt" (rj (generate (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 5))) (.leaf 6)) (localColor (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6)) (.both [] [false])) 6))
#eval emit "actual_two_vertex_clear/internal_guard" (Lean.toJson ([!((leafList (leaves (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6))) (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6))).contains []),!((leafList (leaves (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6))) (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) (.node (.leaf 4) (.leaf 5))) (.leaf 6))).contains [false])]))
#eval emit "singleton_root_is_nonlabel" (Lean.toJson (!((leafList [7] (.leaf 7)).contains [])))
