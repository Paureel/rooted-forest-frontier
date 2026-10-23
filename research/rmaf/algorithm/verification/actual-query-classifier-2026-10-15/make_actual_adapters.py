from pathlib import Path
import json
b=Path(__file__).resolve().parent
cs=json.loads((b/'CONTROL-PIN.json').read_text())['controls']
s=lambda v:json.dumps(v,ensure_ascii=False)
lst=lambda xs:'['+','.join(xs)+']'
def tree(x):return f'(.leaf {x})' if isinstance(x,int) else f'(.node {tree(x[0])} {tree(x[1])})'
q='''import Work
open Lean Universal233.PaidQueries
def js (x : String) : Json := toJson x
def jobJ (p : Nat × String) : Json := Json.arr #[toJson p.1,toJson p.2]
def witness (p : Nat × String) (m : Nat) : Json := Json.arr #[js "slot",toJson p.1,js p.2,js "minimum",toJson m]
def mock (tag : String) (mins : List Nat) (p : Nat × String) (budget : Nat) : Option (Nat × Json) :=
 let m := mins[p.1]!
 let ok := decide (m ≤ budget)
 dbg_trace ("REVIEW_SPY " ++ (Json.mkObj [("tag",js tag),("index",toJson p.1),("slot",js p.2),("budget",toJson budget),("success",toJson ok),("cost",if ok then toJson m else Json.null),("witness",if ok then witness p m else Json.null)]).compress);
 if ok then some (m,witness p m) else none
def quiet (mins : List Nat) (p : Nat × String) (budget : Nat) : Option (Nat × Json) :=
 let m := mins[p.1]!
 if m ≤ budget then some (m,witness p m) else none
def ansJ (a : Option (List (Nat × Json))) : Json := match a with
 | none => Json.null
 | some xs => toJson (xs.map (fun x => Json.arr #[toJson x.1,x.2]))
def checkQuery (id : String) (q : Nat) (mins : List Nat) (jobs : List (Job (Nat × String) Json)) : IO Unit := do
 let r := schedule (mock (id++":actual") mins) q jobs
 let m := meterSchedule (mock (id++":meter") mins) (fun p b => 100*(p.1+1)+b) q jobs
 let raw := run (quiet mins) (allocated q jobs) jobs
 IO.println ("REVIEW_VALUE " ++ (Json.mkObj [("id",js id),("answers",ansJ r.answers),("rawAnswers",ansJ raw.answers),("calls",toJson r.calls),("visits",toJson r.visits),("known",toJson (knownCost jobs)),("pending",toJson (pending jobs)),("bad",toJson (badSlots jobs)),("budget",toJson (allocated q jobs)),("meterAnswers",ansJ m.value.answers),("meterCalls",toJson m.value.calls),("meterVisits",toJson m.value.visits),("queries",toJson (m.queries.map (fun pb => Json.arr #[jobJ pb.1,toJson pb.2]))),("callerWork",toJson m.callerWork),("recursiveWork",toJson m.recursiveWork),("mass",toJson ([ ("2",actualQueryMass 2 q r.calls),("233/100",actualQueryMass (mkRat 233 100) q r.calls),("3",actualQueryMass 3 q r.calls)].map (fun (k,v) => Json.arr #[js k,js (toString v)])))]).compress)
def main : IO Unit := do
'''
for c in cs:
 if c['op']!='query':continue
 d=c['input'];jobs=[]
 for i,r in enumerate(d.get('resolved',[])):jobs.append(f'(.resolved ({i},{s(r["slot"])}) {r["cost"]} (js {s(r["witness"])}))')
 for i,x in enumerate(d['slots']):jobs.append(f'(.hard ({i},{s(x)}))')
 q+=f' checkQuery {s(c["id"])} {d["q"]} {lst(list(map(str,d["minima"])))} {lst(jobs)}\n'
(b/'isolated-query/ReviewActual.lean').write_text(q)
r='''import Lean
import OptimizedWork
open Lean RMAF Universal233 Universal233.CoreProgram Universal233.CoreWork Universal233.SourceCoverage Universal233.RankConsumer Universal233.RankDichotomy
def outJ (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map (fun v => String.ofList (v.map (fun x => if x then '1' else '0')))))]
def tracedColor (tag : String) (x : Nat) : Nat :=
 dbg_trace ("REVIEW_COLOR " ++ (Json.mkObj [("tag",toJson tag),("label",toJson x),("color",toJson (x/2))]).compress);
 x/2
def checkRank (id : String) (t : Tree) : IO Unit := do
 let v := inputRank t (tracedColor (id++":rank"))
 IO.println ("REVIEW_VALUE " ++ (Json.mkObj [("id",toJson id),("rank",toJson v)]).compress)
def checkFour (id : String) (t : Tree) (q : Nat) : IO Unit := do
 let out := optimizedFourOutputs t (tracedColor (id++":actual")) q
 let m := meterOptimizedFour t (tracedColor (id++":meter")) q
 let raw := generate t (fun x => x/2) q
 let probe := fourProbe t (fun x => x/2)
 IO.println ("REVIEW_VALUE " ++ (Json.mkObj [("id",toJson id),("outputs",toJson (out.map outJ)),("meterOutputs",toJson (m.outputs.map outJ)),("rawOutputs",toJson (raw.outputs.map outJ)),("probeOutputs",toJson (probe.outputs.map outJ)),("colorCalls",toJson m.colorCalls),("work",toJson m.work),("rawPruned",toJson raw.pruned),("probePruned",toJson probe.pruned),("fixedProbeBound",toJson (fixedProbeBound t)),("fullCoreBound",toJson (fullCoreBound t q)),("mass",toJson ([("2",rawQMass 2 out),("233/100",rawQMass (mkRat 233 100) out),("3",rawQMass 3 out)].map (fun (k,v) => Json.arr #[toJson k,toJson (toString v)])))]).compress)
def main : IO Unit := do
'''
for c in cs:
 if c['op']=='classify':r+=f' checkFour {s(c["id"])} {tree(c["input"]["source"])} {c["input"]["q"]}\n'
 if c['op']=='rank':r+=f' checkRank {s(c["id"])} {tree(c["input"]["source"])}\n'
(b/'isolated-rank/ReviewActual.lean').write_text(r)
print('Created independent adapters:16 query and16 classifier plus1 generic rank fixtures. dbg_trace is instrumentation only, not a proof of effects or a hidden solver.')
