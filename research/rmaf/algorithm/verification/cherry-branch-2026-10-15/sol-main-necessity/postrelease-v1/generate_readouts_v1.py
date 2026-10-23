#!/usr/bin/env python3
"""Generate independent test calls to exact source; expectations remain untouched."""
import json
from pathlib import Path
P=Path(__file__).resolve().parent; B=P.parent
expect=json.loads((B/'EXPECTATIONS-v1.json').read_text())
def tr(t): return f'(.leaf {t})' if isinstance(t,int) else f'(.node {tr(t[0])} {tr(t[1])})'
def lists(x): return '['+','.join(lists(a) if isinstance(a,list) else str(a) for a in x)+']'
source='''import Unordered
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
 ("sourceVertices",addrs (Integration.vertices S)),
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
'''
cases=[]
for c in expect['cases']:
    F=c.get('F',c['P']); G=c.get('G',c['P'])
    cases.append(f'caseJSON {json.dumps(c["id"])} {tr(c["T"])} {tr(c["S"])} {c["a"]} {c["b"]} {lists(F)} {lists(G)}')
priorities=[f'priorityJSON {json.dumps(c["id"])} {tr(c["T"])} {tr(c["S"])}' for c in expect['priority_cases']]
fixture=json.loads((B/'CHILD-FIXTURE-v1.json').read_text()); c=next(c for c in expect['cases'] if c['id']=='t3-new')
source+='\ndef mockSource : Tree := '+tr(c['S'])+'\n'
source+='def mockSolver (c : Child) (r : Nat) : Option (List (List Nat)) :=\n'
source+=' if c == singletonChild mockSource 0 then if 1 ≤ r then some '+lists(fixture['children'][0]['G'])+' else none\n'
source+=' else if c == singletonChild mockSource 1 then some '+lists(fixture['children'][1]['G'])+'\n'
source+=' else if c == pendantChild mockSource 0 1 then some '+lists(fixture['children'][2]['G'])+' else none\n'
source+='def callsJSON : List Json := (List.range 4).flatMap fun k => (branches mockSource 0 1).map fun c => Json.mkObj [("k",toJson k),("paid",toJson c.paid),("P",toJson c.partition),("remaining",toJson (remaining k c)),("result",toJson (childCall mockSolver k c))]\n'
source+='def main : IO Unit := IO.println ((Json.mkObj [("cases",toJson ['+',\n'.join(cases)+']),("priority",toJson ['+',\n'.join(priorities)+']),("calls",toJson callsJSON)]).compress)\n'
(P/'Readouts_v1.lean').write_text(source)
print(json.dumps({'literal_cases':len(cases),'priority_cases':len(priorities),'calls':12,'expectations_changed':False}))
