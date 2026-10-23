#!/usr/bin/env python3
"""One-shot compiled observer of unchanged READY fixtures; no query implementation."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;READY=P.parent/'sol-preparation-READY-v1/preparation';data=json.loads((READY/'fixtures-v1.json').read_text())
base='''import Lean
import SelectedHigh
open Lean RMAF CoreProgram SourceCoverage VertexGeometry BinaryExchange PairAssembly RankDichotomy RankConsumer
open Universal233 Universal233.BinaryCheap
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace IndependentReadout

def addr (p : RMAF.Vertex) : String := String.ofList (p.map (fun b => if b then '1' else '0'))
def treeJson : Tree → Json
 | .leaf x => toJson x
 | .node a b => Json.arr #[treeJson a,treeJson b]
def optionTree (t : Option Tree) : Json := match t with
 | none => Json.null
 | some s => treeJson s

def outputJson (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("sourceCuts",toJson (o.sourceCuts.map addr))]
def receiptJson (r : Receipt) : Json := Json.mkObj [("outputs",toJson (r.outputs.map outputJson)),("refusals",toJson r.refusals),("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def hull (T : Tree) (A : List Nat) : List String := ((minimalVertices A T).map addr).mergeSort

def sameMembers (A B : List Nat) : Bool := A.all B.contains && B.all A.contains

def localJson (S T : Tree) (A : List Nat) : Json :=
 let s := restrict A S
 let t := restrict A T
 let res := match s,t with
 | some s,some t =>
   let r := DepthOne.pretest01 t s
   match r with
   | .refused => Json.mkObj [("kind",toJson "refused")]
   | .rejected => Json.mkObj [("kind",toJson "rejected")]
   | .found c => Json.mkObj [("kind",toJson "found"),("cuts",toJson ((DepthOne.sourceCuts c).map addr)),("partition",toJson (DepthOne.forest s c)),("agreement",toJson (agreement t s (DepthOne.forest s c))),("cost",toJson (DepthOne.cutCost c))]
 | _,_ => Json.mkObj [("kind",toJson "absent")]
 Json.mkObj [("S",optionTree s),("T",optionTree t),("result",res)]

def selector (T : Tree) (A B : List Nat) : Json := match PairGeometry.choose T A B with
 | none => Json.null
 | some (.vertex v) => Json.mkObj [("kind",toJson "vertex"),("vertex",toJson (addr v))]
 | some (.edge e) => Json.mkObj [("kind",toJson "edge"),("edge",toJson [addr e.1,addr e.2])]

def disj (T : Tree) (A B : List Nat) : Bool := disjointVertices (minimalVertices A T) (minimalVertices B T)
def refined (Q P : List (List Nat)) : Bool := Q.all (fun b => P.any (fun a => b.all a.contains))
def rational (v : Rat) : Json := Json.mkObj [("num",toJson v.num),("den",toJson v.den)]

def outputFacts (S T : Tree) (A B C : List Nat) (o : Output) : Json := Json.mkObj [
 ("output",outputJson o),("partition_source",toJson (partitionCheck (leaves S) o.partition)),
 ("source_embeddings",toJson (pairwiseEmbeddings S o.partition)),("target_embeddings",toJson (pairwiseEmbeddings T o.partition)),
 ("agreement",toJson (agreement S T o.partition)),("parent_refinement",toJson (refined o.partition [A,B,C])),
 ("source_hulls",toJson (o.partition.map (hull S))),("target_hulls",toJson (o.partition.map (hull T))),
 ("blocks",toJson (o.partition.map (fun K => Json.mkObj [("labels",toJson K),("good",toJson (restrictionAgrees S T K)),("local",localJson S T K)])))]

def caseJson (id : String) (S T : Tree) (A B C : List Nat) (e : RMAF.Vertex) : Json := Id.run do
 let D := PairGeometry.descendants T e
 let ca := cheapColor A B D
 let cb := cheapColor B A D
 let q := (leaves S).length+2
 let ra := generate S ca q
 let rb := generate S cb q
 let app := sideOutputs S B A D q ++ sideOutputs S A B D q
 let budgets := (List.range (q+1)).map (fun n => Json.mkObj [("q",toJson n),("A",receiptJson (generate S ca n)),("B",receiptJson (generate S cb n))])
 return Json.mkObj [
 ("id",toJson id),("S",treeJson S),("T",treeJson T),("P",toJson [A,B,C]),("edge",toJson (addr e)),
 ("selector",selector T A B),("selector_swap",selector T B A),
 ("source_nodup",toJson (decide (leaves S).Nodup)),("target_nodup",toJson (decide (leaves T).Nodup)),
 ("same_labels",toJson (decide ((leaves S).Perm (leaves T)))),("partition_P",toJson (partitionCheck (leaves S) [A,B,C])),
 ("source_P",toJson (pairwiseEmbeddings S [A,B,C])),("A_good",toJson (restrictionAgrees S T A)),("B_good",toJson (restrictionAgrees S T B)),("C_good",toJson (restrictionAgrees S T C)),
 ("C_clear",toJson (disj T A C && disj T B C)),("sectors",toJson [ay A D,an A D,ay B D,an B D]),
 ("sector_good",toJson ([ay A D,an A D,ay B D,an B D].map (restrictionAgrees S T))),
 ("rank",toJson [inputRank S ca,inputRank S cb]),("probe",toJson [fourAccepted S ca,fourAccepted S cb]),
 ("classes_A",toJson (classes A B C D)),("classes_B",toJson (classes B A C D)),
 ("colors_A",toJson ((leaves S).map (fun z => [z,ca z]))),("colors_B",toJson ((leaves S).map (fun z => [z,cb z]))),
 ("calls",Json.mkObj [("A",receiptJson ra),("B",receiptJson rb)]),("budgets",toJson budgets),
 ("output_facts",Json.mkObj [("A",toJson (ra.outputs.map (outputFacts S T A B C))),("B",toJson (rb.outputs.map (outputFacts S T A B C)))]),
 ("local_A",localJson S T A),("local_B",localJson S T B),
 ("appended_raw",toJson (app.map outputJson)),("masses",toJson ([2,(233/100 : Rat),3].map (fun c => Json.mkObj [("c",rational c),("value",rational (rawQMass c app)),("raw_denominator",toJson app.length)])))]

def emit (j : Json) : IO Unit := IO.println ("READOUT_JSON " ++ j.compress)
end IndependentReadout
'''
(P/'src/IndependentReadout.lean').write_text(base)
def tree(t):return '.leaf '+str(t)if isinstance(t,int)else '(.node ('+tree(t[0])+') ('+tree(t[1])+'))'
def ls(x):return '['+','.join(map(str,x))+']'
def edge(e):return '['+','.join('true'if x=='1'else'false'for x in e)+']'
def command(f):
 return '#eval IndependentReadout.emit (IndependentReadout.caseJson '+json.dumps(f['id'])+' ('+tree(f['S'])+') ('+tree(f['T'])+') '+''.join(ls(b)+' 'for b in f['P'])+edge(f['edge'])+')\n'
# Pure, hand-known primitive controls precede scientific fixture evaluation.
prim='''import IndependentReadout
#eval IndependentReadout.emit (Json.mkObj [("primitive",Lean.toJson "topology"),("same",Lean.toJson (RMAF.restrictionAgrees (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) [0,1,2])),("wrong",Lean.toJson (RMAF.restrictionAgrees (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) [0,1,2]))])
'''
(P/'src/ReadoutPrimitives.lean').write_text(prim)
(P/'src/ReadoutPilot.lean').write_text('import IndependentReadout\n'+command(data['fixtures'][0]))
more=data['fixtures'][1:]+data['outside']+[data['reused_public_false_control']]
for n,e in [('root',''),('leaf','000'),('absent','111111')]:
 f=json.loads(json.dumps(data['fixtures'][0]));f['id']='frozen-invalid-'+n+'-edge';f['edge']=e;more.append(f)
(P/'src/ReadoutBattery.lean').write_text('import IndependentReadout\n'+''.join(command(f)for f in more))
for name,f in data['primitive_controls'].items():
 if 'colors'in f:
  col='(fun z => '+''.join('if z == '+k+' then '+str(v)+' else 'for k,v in f['colors'].items())+'0)'
  with (P/'src/ReadoutPrimitives.lean').open('a')as o:o.write('#eval IndependentReadout.emit (Json.mkObj [("primitive",Lean.toJson '+json.dumps(name)+'),("receipt",IndependentReadout.receiptJson (CoreProgram.generate ('+tree(f['S'])+') '+col+' '+str(f['q'])+'))])\n')
freeze={'fixtures_sha256':hashlib.sha256((READY/'fixtures-v1.json').read_bytes()).hexdigest(),'expectations_unchanged':True,'before_execution':True,'sources':[{'path':n,'sha256':hashlib.sha256((P/'src'/n).read_bytes()).hexdigest()}for n in ['IndependentReadout.lean','ReadoutPrimitives.lean','ReadoutPilot.lean','ReadoutBattery.lean']],
'pilot':'primitive known-answer controls, then first frozen hand fixture; only then fixed remainder','candidate_source_mutations':0,'lineage':'Actual compiled definitions observed; reference is unchanged own READY graph/generator/oracle lineage.'}
(P/'compiled-readout-freeze-v1.json').write_text(json.dumps(freeze,indent=2)+'\n');print('Observer frozen for primitives, one-fixture pilot and fixed battery.')
