"""One-shot actual value/diagnostic adapter, not candidate production code.
Traced blockColor substitution is a separate generator diagnostic,never called
an effect trace of hardcoded recover. Literal inputs come only from frozen PIN.
"""
from pathlib import Path
import json,importlib.util,sys
b=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('final_cut_adapter_old',b/'frozen-inputs/original_graph.py');old=importlib.util.module_from_spec(spec);sys.modules[spec.name]=old;spec.loader.exec_module(old)
cs=json.loads((b/'CONTROL-PIN.json').read_text())['controls'];s=json.dumps
def tree(x):return f'(.leaf {x})' if isinstance(x,int) else f'(.node {tree(x[0])} {tree(x[1])})'
def ls(xs):return '['+','.join(map(str,xs))+']'
def blocks(p):return '['+','.join(ls(x) for x in p)+']'
def vertex(p):return '['+','.join('true' if x=='1' else 'false' for x in p)+']'
def vertices(ps):return '['+','.join(vertex(p) for p in ps)+']'
code='''import Lean
import FinalWork
open Lean RMAF Universal233 Universal233.CoreGraph Universal233.CoreProgram Universal233.CoreWork Universal233.FinalCutRecovery Universal233.RankDichotomy Universal233.SourceCoverage
def addr (v : RMAF.Vertex) : String := String.ofList (v.map (fun x => if x then '1' else '0'))
def outJ (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("cuts",toJson (o.sourceCuts.map addr))]
def optionJ : Option Output → Json | none => Json.null | some o => outJ o
def tracedColor (tag : String) (p : List (List Nat)) (x : Nat) : Nat :=
 let c := blockColor p x
 dbg_trace ("COLOR_DIAGNOSTIC " ++ (Json.mkObj [("tag",toJson tag),("label",toJson x),("color",toJson c)]).compress);
 c
def checkRecovery (id : String) (t target : Tree) (p : List (List Nat)) : IO Unit := do
 let actual := recover t p
 let metered := meterRecover t p
 let valid := inputCheck t p
 let raw := if valid then generate t (blockColor p) (p.length-1) else ({} : Receipt)
 let traced := if valid then generate t (tracedColor id p) (p.length-1) else ({} : Receipt)
 let colorViews := if valid then (leaves t).map (fun x => Json.mkObj [("label",toJson x),("color",toJson (blockColor p x)),("meterColor",toJson (meterColor p x).value),("meterWork",toJson (meterColor p x).work)]) else []
 let rank := if valid then some (inputRank t (blockColor p)) else none
 let mcore := if valid then some (meterGenerate t (blockColor p) (p.length-1)) else none
 IO.println ("ACTUAL_VALUE " ++ (Json.mkObj [("id",toJson id),("recover",optionJ actual),("meterRecover",optionJ metered.value),("inputCheck",toJson valid),("distinct",toJson (decide (leaves t).Nodup)),("partitionCheck",toJson (partitionCheck (leaves t) p)),("embeddings",toJson (pairwiseEmbeddings t p)),("minimalVertices",toJson (p.map (fun b => (minimalVertices b t).map addr))),("rawOutputs",toJson (raw.outputs.map outJ)),("tracedDiagnosticOutputs",toJson (traced.outputs.map outJ)),("colors",toJson colorViews),("rankDiagnostic",toJson rank),("coreColorCalls",toJson (mcore.map (fun x => x.oracleCalls))),("visited",toJson raw.visited),("attempts",toJson raw.childAttempts),("pruned",toJson raw.pruned),("refusals",toJson raw.refusals),("meterWork",toJson metered.work),("guardCharge",toJson (guardCharge t p)),("colorCharge",toJson (colorCharge t p)),("finalPolynomial",toJson (finalPolynomial t p)),("nodes",toJson (treeNodes t)),("targetAgreement",toJson (agreement target t p)),("returnedTargetAgreement",toJson (actual.map (fun o => agreement target t o.partition)))]).compress)
def validAddress (t : Tree) (v : RMAF.Vertex) : Bool := (subtree t v).isSome
def actualEdge (t : Tree) (u v : RMAF.Vertex) : Bool :=
 validAddress t u && validAddress t v && ((v.dropLast==u && v.length==u.length+1) || (u.dropLast==v && u.length==v.length+1))
def checkCertificate (id : String) (t : Tree) (vs cuts : List RMAF.Vertex) : IO Unit := do
 IO.println ("ACTUAL_VALUE " ++ (Json.mkObj [("id",toJson id),("validOriginalVertices",toJson (vs.map (fun v => validAddress t v))),("nodes",toJson (treeNodes t)),("cutEdges",toJson (cuts.map (fun v => v != [] && actualEdge t v.dropLast v))),("reverseEdges",toJson (cuts.map (fun v => v != [] && actualEdge t v v.dropLast)))]).compress)
def checkEdges (id : String) (t : Tree) (pairs : List (RMAF.Vertex × RMAF.Vertex)) : IO Unit := do
 IO.println ("ACTUAL_VALUE " ++ (Json.mkObj [("id",toJson id),("actual",toJson (pairs.map (fun (u,v) => actualEdge t u v)))]).compress)
def checkAbsorb (id : String) (k q calls : Nat) (c : Rat) : IO Unit := do
 IO.println ("ACTUAL_VALUE " ++ (Json.mkObj [("id",toJson id),("factor",toJson (2^k)),("charged",toJson (calls*2^k)),("absorbed",toJson (decide ((calls : Rat)*(2 : Rat)^k<=c^q)))]).compress)
def main : IO Unit := do
'''
for c in cs:
 d=c['input'];ident=s(c['id'])
 if c['op']=='recover':code+=f' checkRecovery {ident} {tree(d["tree"])} {tree(d.get("target",d["tree"]))} {blocks(d["partition"])}\n'
 elif c['op']=='certificate':code+=f' checkCertificate {ident} {tree(d["tree"])} {vertices(sorted(old.Graph(d["tree"]).at))} {vertices(d["cuts"])}\n'
 elif c['op']=='edges':code+=f' checkEdges {ident} {tree(d["tree"])} ['+','.join(f'({vertex(u)},{vertex(v)})' for u,v in d['pairs'])+']\n'
 elif c['op']=='absorption':
  base=d['c'].split('/');rat=f'(mkRat {base[0]} {base[1]})' if len(base)==2 else base[0]
  code+=f' checkAbsorb {ident} {d["k"]} {d["q"]} {d["calls"]} {rat}\n'
(b/'isolated/ReviewActual.lean').write_text(code)
print('Created22 actual recover calls,16 original-address diagnostics,1 edge trap,5 literal absorption cases.2 permutation checks remain graph/list relations; no runtime permutation scan is inserted.')
