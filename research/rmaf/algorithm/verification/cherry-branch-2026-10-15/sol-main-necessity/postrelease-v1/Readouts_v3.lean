import Unordered
import Lean
open Lean RMAF Universal233.CherryBranching
def address (v : RMAF.Vertex) : String := String.ofList (v.map fun b => if b then '1' else '0')
def addrs (vs : List RMAF.Vertex) : Json := toJson (vs.map address)
def treeJSON : Tree → Json
 | .leaf x => toJson x
 | .node l r => Json.arr #[treeJSON l,treeJSON r]
def childJSON (c : Child) : Json := Json.mkObj [
 ("P",toJson c.partition),("paid",toJson c.paid),
 ("sourceForest",toJson (c.sourceForest.map treeJSON)),("sourceCount",toJson c.sourceForest.length)]
def refineB (F P : List (List Nat)) : Bool := F.all fun B => P.any fun C => B.all C.contains
def caseJSON (id : String) (T S : Tree) (a b : Nat) (F G : List (List Nat)) : Json :=
 let c := pendantChild S a b
 Json.mkObj [("id",toJson id),("cuts",addrs (cuts S a b)),
 ("P",toJson c.partition),("roots",addrs (componentRoots S a b)),
 ("minimalVertices",addrs (minimalVertices [a,b] S)),
 ("sourceVertices",addrs (Universal233.HardParent.vertices S)),
 ("pendantChild",childJSON c),
 ("endpointA",match endpointBranch S a with | some br => Json.mkObj [("cuts",addrs br.originalCuts),("child",childJSON br.child)] | none => Json.null),
 ("endpointB",match endpointBranch S b with | some br => Json.mkObj [("cuts",addrs br.originalCuts),("child",childJSON br.child)] | none => Json.null),
 ("Fagreement",toJson (agreement T S F)),("Gagreement",toJson (agreement T S G)),
 ("Frefines",toJson (refineB F c.partition)),("Grefines",toJson (refineB G c.partition)),
 ("Fstate",toJson (ForestState.agrees (some T) c.sourceForest F)),
 ("Gstate",toJson (ForestState.agrees (some T) c.sourceForest G)),
 ("remaining",toJson ((List.range 5).map fun k => remaining k c))]
def priorityJSON (id : String) (T S : Tree) : Json :=
 let cs := candidates T S
 Json.mkObj [("id",toJson id),("counts",toJson (cs.map fun c => c.originalCuts.length)),
 ("candidates",toJson (cs.map fun c => Json.mkObj [("parent",toJson (address c.parent)),("pair",toJson [c.a,c.b]),("cuts",addrs c.originalCuts)])),
 ("selected",match select T S with
  | none => Json.null
  | some (pr,c) => Json.mkObj [("category",toJson (match pr with | .common => "common" | .one => "t1" | .high => "high" | .hard2 => "hard2")),("pair",toJson [c.a,c.b]),("cuts",addrs c.originalCuts)])]

def mockSource : Tree := (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.leaf 1))
def mockSolver (c : Child) (r : Nat) : Option (List (List Nat)) :=
 if c == singletonChild mockSource 0 then if 1 ≤ r then some [[0],[1],[2,3,4]] else none
 else if c == singletonChild mockSource 1 then some [[0,2,3,4],[1]]
 else if c == pendantChild mockSource 0 1 then some [[0,1],[2],[3],[4]] else none
def callsJSON : List Json := (List.range 4).flatMap fun k => (branches mockSource 0 1).map fun c => Json.mkObj [("k",toJson k),("paid",toJson c.paid),("P",toJson c.partition),("remaining",toJson (remaining k c)),("result",toJson (childCall mockSolver k c))]
def main : IO Unit := IO.println ((Json.mkObj [("cases",toJson [caseJSON "common" (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) 0 1 [[0,1,2]] [[0,1,2]],
caseJSON "t1-public" (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) 0 1 [[0,2],[1]] [[0,1],[2]],
caseJSON "t2-new" (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 1)) 0 1 [[2],[3],[0,1]] [[2],[3],[0,1]],
caseJSON "t3-new" (.node (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.node (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.leaf 1)) 0 1 [[0,2,3,4],[1]] [[2],[3],[4],[0,1]],
caseJSON "root-boundary" (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 9)) (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) (.leaf 9)) 0 1 [[0,2,9],[1]] [[0,1,9],[2]],
caseJSON "swapped" (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))) (.node (.leaf 1) (.node (.leaf 2) (.leaf 0))) 0 1 [[2],[0,1]] [[2],[0,1]],
caseJSON "arbitrary-nat" (.node (.node (.leaf 7) (.leaf 1000)) (.leaf 42)) (.node (.node (.leaf 7) (.leaf 42)) (.leaf 1000)) 7 1000 [[42],[7,1000]] [[42],[7,1000]]]),("priority",toJson [priorityJSON "common-before-earlier-t1" (.node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 2) (.leaf 3)) (.leaf 4))) (.node (.node (.node (.leaf 0) (.leaf 4)) (.leaf 1)) (.node (.leaf 2) (.leaf 3))),
priorityJSON "high-before-earlier-hard2" (.node (.node (.leaf 2) (.leaf 3)) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 4))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.node (.leaf 1) (.leaf 4)) (.leaf 3))),
priorityJSON "t1-before-hard2" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1)) (.leaf 3)),
priorityJSON "only-hard2" (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))),
priorityJSON "empty" (.leaf 0) (.leaf 0)]),("calls",toJson callsJSON)]).compress)
