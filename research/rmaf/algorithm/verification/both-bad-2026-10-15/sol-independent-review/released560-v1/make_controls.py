#!/usr/bin/env python3
"""Generate compiled adapters from unchanged precontact literal input code.
Unsafe IO wrappers are diagnostic probes only; no candidate source is edited.
"""
import importlib.util,json,pathlib,sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('frozen_own',HERE.parent/'instrument-v2.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def tree(t):return f'(.leaf {t})' if isinstance(t,int) else f'(.node {tree(t[0])} {tree(t[1])})'
rows=[]
for variant in ['identity','parent-swap','mirror-both','mirror-source','relabel']:
  for name,source in m.CASES.items():
    x=m.transform(source,variant);label=name if variant=='identity' else name+':'+variant
    p=x['p']; rows.append('('+json.dumps(label)+','+tree(x['s'])+','+tree(x['t'])+','+str(p[0])+','+str(p[1])+','+str(p[2])+')')
text=r'''import BothConsumers
import Lean
open Lean RMAF Universal233 CoreProgram BothBad BinaryCheap RankConsumer

private def tj : Tree → Json
  | .leaf n => toJson n
  | .node a b => .arr #[tj a,tj b]
private def targetj (t : Option Tree) : Json := t.map tj |>.getD .null
private def aj (v : RMAF.Vertex) : Json := .str (String.ofList (v.map fun b => if b then '1' else '0'))
private def oj (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("cuts",.arr (o.sourceCuts.toArray.map aj))]
private def rj (r : CoreProgram.Receipt) : Json := Json.mkObj [
  ("outputs",.arr (r.outputs.toArray.map oj)),("refusals",toJson r.refusals),
  ("visited",toJson r.visited),("attempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
private def cj (c : BothBad.Call) : Json := Json.mkObj [
  ("target",targetj c.target),("sources",.arr (c.sources.toArray.map tj)),("budget",toJson c.budget)]
private def mj : BothBad.Mode → Json
  | .ordinary => .str "ordinary"
  | .full => .str "full"
  | .retained a b c f => Json.mkObj [("mode",.str "retained"),("parent",toJson a),
      ("residual",toJson b),("completed",toJson c),("known",toJson f)]
private def ej (e : BothBad.Entry) : Json := Json.mkObj [("output",oj e.output),("mode",mj e.mode),("budget",toJson e.budget)]
private def sj : Option PairGeometry.Choice → Json
  | none => .null
  | some (.vertex v) => .arr #[.str "vertex",aj v]
  | some (.edge (u,v)) => .arr #[.str "edge",aj u,aj v]

private def fixedTB : Tree := .node (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6))) (.node (.leaf 7) (.leaf 8))
private def fixedSB : Tree := .node (.node (.node (.leaf 3) (.leaf 4)) (.leaf 7)) (.node (.node (.leaf 5) (.leaf 6)) (.leaf 8))
private def forest0 : List Tree := [.node (.leaf 5) (.leaf 6),.node (.leaf 3) (.leaf 4),.node (.leaf 7) (.leaf 8)]
private def forest1 : List Tree := [.leaf 8,.leaf 7,.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6))]
private def oracle (kind : Nat) (t : Option Tree) (ss : List Tree) (b : Nat) : Option Forest :=
  if kind=1 then some [] else
  if kind=2 then some ((ss.flatMap leaves).map (fun x => [x])) else
  if kind=3 then
    if t=some fixedTB ∧ ss=[fixedSB] ∧ b=3 then some [[3,4],[5],[6],[7,8]] else
    if t=some fixedTB ∧ ss=forest0 ∧ b=1 then some [[5],[6],[3,4],[7,8]] else
    if t=some fixedTB ∧ ss=forest1 ∧ b=1 then none else none
  else none

@[noinline] private unsafe def logged (ref : IO.Ref (List BothBad.Call)) (kind : Nat)
    (t : Option Tree) (ss : List Tree) (b : Nat) : Option Forest := unsafeBaseIO do
  ref.modify (fun xs => xs++[⟨t,ss,b⟩])
  return oracle kind t ss b

private unsafe def execution (s t : Tree) (a b c : List Nat) (edge : RMAF.Vertex×RMAF.Vertex)
    (q kind : Nat) : IO Json := do
  let ref ← IO.mkRef ([] : List BothBad.Call)
  let result := solvePair (logged ref kind) s t a b c edge q
  let out := Json.mkObj [("answer",toJson result.answer),("reported_calls",.arr (result.calls.toArray.map cj))]
  -- Force result construction and payload use before reading the diagnostic log.
  let encoded := out.compress
  let observed ← ref.get
  return Json.mkObj [("q",toJson q),("oracle",toJson kind),("result",.str encoded),
    ("observed_calls",.arr (observed.toArray.map cj))]

private def cases : List (String×Tree×Tree×List Nat×List Nat×List Nat) := [
CASES
]

private unsafe def schedulerControl (label : String) (jobs : List Nat) : IO Json := do
  let ref ← IO.mkRef ([] : List Nat)
  let fn := fun p b => unsafeBaseIO do
    ref.modify (fun xs => xs++[p])
    return if label="failed" || (label="early_failure" && p=1) then none else some (0,([] : Forest))
  let receipt := PaidQueries.meterSchedule fn (fun _ _ => 0) (2*jobs.length) (jobs.map PaidQueries.Job.hard)
  let queries := receipt.queries
  let result := Json.mkObj [("label",.str label),("queries",toJson queries),
    ("answer",toJson receipt.value.answers),("work",toJson receipt.callerWork)]
  let encoded := result.compress
  let observed ← ref.get
  return Json.mkObj [("result",.str encoded),("observed",toJson observed)]

unsafe def main (args : List String) : IO Unit := do
  let pilot := args.contains "pilot"
  let selected := if pilot then cases.take 2 else cases
  let mut results : Array Json := #[]
  for (name,s,t,a,b,c) in selected do
    let choice := PairGeometry.choose t a b
    let mut core : Array (String×Json) := #[]
    let mut plans : Array Json := #[]
    let mut executions : Array Json := #[]
    if let some (.edge edge) := choice then
      let d := PairGeometry.descendants t edge.2
      for q in [3,4,5] do
        core := core.push ("splitA-q"++toString q,rj (generate s (cheapColor a b d) q))
        core := core.push ("splitB-q"++toString q,rj (generate s (cheapColor b a d) q))
      for q in [2,3,4,5,6] do
        plans := plans.push (Json.mkObj [("q",toJson q),("entries",.arr ((plan s t a b c d q).toArray.map ej)),
          ("charged",toJson (chargedCosts (plan s t a b c d q))),
          ("budgets",toJson (budgets (plan s t a b c d q)))])
        for kind in (if name="S11" then [0,1,2,3] else [0,1,2]) do
          executions := executions.push (← execution s t a b c edge q kind)
    results := results.push (Json.mkObj [("name",.str name),("selector",sj choice),("cores",Json.mkObj core.toList),
      ("plans",.arr plans),("executions",.arr executions)])
  let mut scheduler : Array Json := #[]
  for (name,js) in [("empty",[]),("failed",[0]),("duplicate",[0,0]),("early_failure",[0,1,2])] do
    scheduler := scheduler.push (← schedulerControl name js)
  IO.println (Json.mkObj [("cases",.arr results),("scheduler",.arr scheduler)]).compress
'''.replace('CASES',',\n'.join(rows))
(HERE/'build/CompiledControls.lean').write_text(text)
print(json.dumps({'cases':len(rows),'output':str(HERE/'build/CompiledControls.lean')}))
