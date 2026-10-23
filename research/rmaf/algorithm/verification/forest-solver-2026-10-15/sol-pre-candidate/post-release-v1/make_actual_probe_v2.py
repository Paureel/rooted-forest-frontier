#!/usr/bin/env python3
"""Generate finite mock ordinary tables from the frozen fresh graph route.

Post-contact instrumentation uses actual candidate calls. These finite tables
are fixtures only; they are not a complete solver or a proof of OrdinaryIH.
"""
from itertools import combinations
import json
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from graph_partition_v2 import Graph,State
spec=json.loads((HERE.parent/'EXPECTATIONS-v1.json').read_text())
supp=json.loads((HERE.parent/'EXPECTATIONS-v2-supplement.json').read_text())
cases=[]
for old in spec['cases']:
    c=dict(old)
    if c['id']=='three_region':c.update(supp['three_region'])
    if not c['proper']:c['budgets']=[0,1]
    cases.append(c)
def ren(t):return 37*t+11 if isinstance(t,int) else [ren(t[1]),ren(t[0])]
for c in cases[:3]:
    for rev in [False,True]:
        cases.append({**c,'id':c['id']+'_large_'+str(int(rev)),
          'T':ren(c['T']),'ss':[ren(s) for s in (list(reversed(c['ss'])) if rev else c['ss'])],
          'witness':[[37*x+11 for x in b] for b in c['witness']]})
cases.append({'id':'one_source_hard','T':[[0,2],[1,3]],'ss':[[[0,1],[2,3]]],
              'proper':True,'minimum':2,'budgets':[1,2,3],'affordable':[False,True,True],
              'origin':'pre-frozen sole-hard ordinary restriction; extra post-contact call-site instrumentation'})
table=[];seen=set()
for c in cases:
    if not c['proper']:continue
    for source in c['ss']:
        gs=Graph(source);gt=Graph(c['T'])
        for k in range(1,len(gs.taxa)+1):
            for subset in combinations(gs.taxa,k):
                t=gt.restriction(subset);s=gs.restriction(subset)
                key=(str(Graph(t).topology(subset)),str(Graph(s).topology(subset)))
                if key in seen:continue
                seen.add(key)
                state=State(t,[s]);minimum,valid=state.exact()
                assert minimum is not None
                winner=min(valid,key=len)
                table.append({'target':t,'source':s,'minimum':minimum,'forest':winner})
def tree(t):
    return '.leaf '+str(t) if isinstance(t,int) else '(.node ('+tree(t[0])+') ('+tree(t[1])+'))'
def forest(f):return '['+','.join('['+','.join(map(str,b))+']' for b in f)+']'
def trees(ss):return '['+','.join('('+tree(s)+')' for s in ss)+']'
tablecode='[\n'+',\n'.join('('+tree(r['target'])+','+tree(r['source'])+','+str(r['minimum'])+','+forest(r['forest'])+')' for r in table)+'\n]'
casecode='[\n'+',\n'.join('('+json.dumps(c['id'])+','+('none' if c['T'] is None else 'some ('+tree(c['T'])+')')+','+trees(c['ss'])+','+'['+','.join(map(str,c['budgets']))+'])' for c in cases)+'\n]'
template=r'''import ForestResource
import Lean
open Lean RMAF ForestState GenericForest
open Universal233.CoreProgram Universal233.PaidQueries
open VertexGeometry

def mockTable : List (Tree × Tree × Nat × Forest) := __TABLE__

def mockOrdinary (t s : Tree) (q : Nat) : Option Forest :=
  (mockTable.find? fun r => sameShape t r.1 && sameShape s r.2.1).bind fun r =>
    if r.2.2.1 ≤ q then some r.2.2.2 else none

def treeJson : Tree → Json
  | .leaf x => toJson x
  | .node a b => Json.arr #[treeJson a,treeJson b]
def targetJson : Option Tree → Json
  | none => Json.null
  | some t => treeJson t
def sourcesJson (ss : List Tree) : Json := Json.arr (ss.toArray.map treeJson)
def vertexJson (v : Vertex) : Json := toJson (v.map fun b => if b then (1:Nat) else 0)
def outputJson (i : Nat) (o : Output) (ss : List Tree) (q : Nat) : Json := Json.mkObj [
  ("parent",toJson i),("partition",toJson o.partition),
  ("sourceCuts",Json.arr (o.sourceCuts.toArray.map vertexJson)),
  ("d",toJson o.sourceCuts.length),("paid_guard",toJson (decide (1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q))),
  ("child_sources",sourcesJson (replace ss i o.partition))]
def generationJson (t s : Tree) (v : Vertex) (q : Nat) : Json :=
  let r := generate s (colorLabel t v) q
  Json.mkObj [("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),
    ("pruned",toJson r.pruned),("refusals",toJson r.refusals),
    ("colors",toJson ((leaves s).map fun x => (x,colorLabel t v x))),
    ("outputs",Json.arr (r.outputs.toArray.map fun o => Json.mkObj [
      ("partition",toJson o.partition),("sourceCuts",Json.arr (o.sourceCuts.toArray.map vertexJson)),
      ("d",toJson o.sourceCuts.length)]))]
def jobJson : Job (Tree × Tree) Forest → Json
  | .hard p => Json.mkObj [("kind",toJson "hard"),("target",treeJson p.1),("source",treeJson p.2)]
  | .resolved p c a => Json.mkObj [("kind",toJson "resolved"),("target",treeJson p.1),
      ("source",treeJson p.2),("cost",toJson c),("forest",toJson a)]

def trace (T : Option Tree) (ss : List Tree) (q : Nat) : List Json :=
  let base := [("T",targetJson T),("ss",sourcesJson ss),("q",toJson q),
    ("actual_return",toJson (GenericForest.solve mockOrdinary T ss q)),
    ("proper",toJson (proper T ss)),("current_agrees",toJson (agrees T ss (ss.map leaves)))]
  if proper T ss then
    if agrees T ss (ss.map leaves) then [Json.mkObj (("case",toJson "done")::base)] else
    match T,ss with
    | none,_ => [Json.mkObj (("case",toJson "none")::base)]
    | some t,[s] => [Json.mkObj ([("case",toJson "singleton"),("query_target",treeJson t),
          ("query_source",treeJson s),("query_budget",toJson q),("ordinary_return",toJson (mockOrdinary t s q))]++base)]
    | some t,_ =>
      match overlap t ss with
      | none =>
        let detail := match jobs t ss with
          | none => [("jobs",Json.null)]
          | some js =>
            let r := meterSchedule (fun p b => (mockOrdinary p.1 p.2 b).map (fun F => (F.length-1,F)))
              (fun _ _ => 0) q js
            [("jobs",Json.arr (js.toArray.map jobJson)),("allocated",toJson (allocated q js)),
              ("knownCost",toJson (knownCost js)),("pending",toJson (pending js)),
              ("query_calls",Json.arr (r.queries.toArray.map fun (p,b) => Json.mkObj [
                ("target",treeJson p.1),("source",treeJson p.2),("budget",toJson b),
                ("answer",toJson (mockOrdinary p.1 p.2 b))])),
              ("meter_answers",toJson r.value.answers),("meter_calls",toJson r.value.calls),
              ("actual_attempt_answers",toJson ((disjointAttempt t ss mockOrdinary q).bind (·.answers))),
              ("meter_callerWork",toJson r.callerWork),("meter_recursiveWork",toJson r.recursiveWork)]
        [Json.mkObj ([("case",toJson "disjoint")]++detail++base)]
      | some h =>
        let raw := branches t ss h q
        let event := Json.mkObj ([("case",toJson "overlap"),("selected_left",toJson h.left),
          ("selected_right",toJson h.right),("selected_vertex",vertexJson h.vertex),
          ("raw",Json.arr (raw.toArray.map fun (i,o) => outputJson i o ss q)),
          ("left_generation",match ss[h.left]? with | none => Json.null | some s => generationJson t s h.vertex q),
          ("right_generation",match ss[h.right]? with | none => Json.null | some s => generationJson t s h.vertex q)]++base)
        event :: (raw.flatMap fun (i,o) =>
          let d := o.sourceCuts.length
          if _hd : 1 ≤ d ∧ d ≤ q then trace T (replace ss i o.partition) (q-d) else [])
  else [Json.mkObj (("case",toJson "improper")::base)]
termination_by q
decreasing_by omega

def cases : List (String × Option Tree × List Tree × List Nat) := __CASES__

def main (args : List String) : IO UInt32 := do
  if args.length != 2 then return 2
  let cs := if args[0]! == "pilot" then cases.take 1 else cases
  let rows := cs.flatMap fun c => c.2.2.2.map fun q =>
    Json.mkObj [("id",toJson c.1),("budget",toJson q),("trace",toJson (trace c.2.1 c.2.2.1 q))]
  IO.FS.writeFile args[1]! ((Json.arr rows.toArray).pretty++"\n")
  IO.println s!"actual probe rows: {rows.length}"
  return 0
'''
(HERE/'ActualProbe-v2.lean').write_text(template.replace('__TABLE__',tablecode).replace('__CASES__',casecode))
(HERE/'actual-probe-inputs-v2.json').write_text(json.dumps({'cases':cases,'mock_table':table,
    'fixture_scope':'finite graph-derived mock ordinary pairs only; not a full solver or OrdinaryIH proof',
    'contact_status':'post-contact instrumentation; original mathematical expectations unchanged'},indent=2)+'\n')
print(json.dumps({'cases':len(cases),'ordinary_table_pairs':len(table)}))
