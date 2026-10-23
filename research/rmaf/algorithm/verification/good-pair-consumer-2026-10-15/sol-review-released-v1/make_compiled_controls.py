#!/usr/bin/env python3
"""Build a value-only compiled control bridge from immutable prerelease fixtures."""
import importlib.util,json,hashlib
from pathlib import Path
P=Path(__file__).resolve().parent;PREP=P.parent/'sol-preparation-READY-v1/preparation'
sp=importlib.util.spec_from_file_location('prep',PREP/'instrument/prepare_graph_controls.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
d=json.loads((PREP/'fixtures-v1.json').read_text())
def tr(t):return f'(.leaf {t})'if isinstance(t,int)else f'(.node {tr(t[0])} {tr(t[1])})'
def l(v):return '['+', '.join(l(z) if isinstance(z,list)or isinstance(z,tuple) else str(z)for z in v)+']'
configs=[]
for f in d['fixtures']:
 s,t=m.x.Graph(f['S']),m.x.Graph(f['T']);fs=[list(map(list,bs)) for bs in m.x.refinements(f['P']) if m.x.agreement(s,t,s.labels,bs)]
 configs.append(f'{{ name := "{f["id"]}", S := {tr(f["S"])}, T := {tr(f["T"])}, A := {l(f["P"][0])}, B := {l(f["P"][1])}, C := {l(f["P"][2])}, qmax := {f["q"]}, knownFs := {l(fs)} }}')
for f in d['premise_corruptions']:
 configs.append(f'{{ name := "{f["id"]}", S := {tr(f["S"])}, T := {tr(f["T"])}, A := {l(f["P"][0])}, B := {l(f["P"][1])}, C := {l(f["P"][2])}, qmax := 0, knownFs := [] }}')
for name,t,A,B in [('singleton-empty-B',0,[0],[]),('absent-B-label',[0,1],[0],[99]),('duplicate-A-label',[0,1],[0,0],[1]),('overlapping-A-B',[0,1],[0],[0]),('duplicate-target-label',[0,0],[0],[1])]:
 configs.append(f'{{ name := "{name}", S := {tr(t)}, T := {tr(t)}, A := {l(A)}, B := {l(B)}, C := [], qmax := 0, knownFs := [] }}')
source='''import Lean
import GoodPair
open Lean RMAF Universal233.CoreProgram VertexGeometry BinaryExchange
open Universal233.PairAssembly Universal233.WholeSourceMass

structure ControlFixture where
  name : String
  S : Tree
  T : Tree
  A : List Nat
  B : List Nat
  C : List Nat
  qmax : Nat
  knownFs : List (List (List Nat))

def fixtures : List ControlFixture := [
'''+',\n'.join(configs)+'''
]
def addr (p : RMAF.Vertex) : String := String.join (p.map (fun b => if b then "1" else "0"))
def outputJson (o : Output) : Json := Json.mkObj [("partition",toJson o.partition),("sourceCuts",toJson (o.sourceCuts.map addr))]
def receiptJson (r : Receipt) : Json := Json.mkObj [
  ("outputs",Json.arr (r.outputs.map outputJson).toArray),("refusals",toJson r.refusals),
  ("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),("pruned",toJson r.pruned)]
def refinesBool (fine coarse : List (List Nat)) : Bool :=
  fine.all (fun b => coarse.any (fun c => b.all (fun x => c.contains x)))
def choiceJson (f : ControlFixture) : Json :=
  match PairGeometry.choose f.T f.A f.B with
  | none => Json.mkObj [("kind",toJson "none")]
  | some (.vertex v) => Json.mkObj [("kind",toJson "vertex"),("vertex",toJson (addr v)),
      ("A_regions",toJson (regions f.A f.T v)),("B_regions",toJson (regions f.B f.T v))]
  | some (.edge e) => Json.mkObj [("kind",toJson "edge"),("parent",toJson (addr e.1)),("child",toJson (addr e.2)),
      ("descendants",toJson (PairGeometry.descendants f.T e.2)),
      ("subtreeLeaves",toJson ((treeAt f.T e.2).map leaves))]
def specs (f : ControlFixture) : List (String × (Nat → Nat)) :=
  match PairGeometry.choose f.T f.A f.B with
  | none => []
  | some (.vertex v) => [("clear-A",taggedColor f.A f.B (colorLabel f.T v) (fun _ => 0) (fun _ => 0)),
      ("clear-B",taggedColor f.A f.B (fun _ => 0) (colorLabel f.T v) (fun _ => 0))]
  | some (.edge e) => [("edge-clear-B",taggedColor f.A f.B (fun _ => 0) (sideColor (PairGeometry.descendants f.T e.2)) (fun _ => 0))]
def compiledFprime (f : ControlFixture) (F : List (List Nat)) : List (List Nat) :=
  match PairGeometry.choose f.T f.A f.B with
  | some (.edge e) => match treeAt f.T e.2 with
      | some u => exchange f.A f.B F u
      | none => F
  | _ => F

def main : IO Unit := do
  for f in fixtures do
    for q in List.range (f.qmax+1) do
      let os := goodPairOutputs f.S f.T f.A f.B q
      let calls := (specs f).map (fun (name,col) => Json.mkObj [("identity",toJson name),
        ("colors",Json.arr ((leaves f.S).map (fun x => Json.arr #[toJson x,toJson (col x)])).toArray),
        ("receipt",receiptJson (generate f.S col q))])
      let fs := f.knownFs.map (fun F =>
        let Fp := compiledFprime f F
        Json.mkObj [("F",toJson F),("Fprime",toJson Fp),("eligible",toJson (decide (F.length-1 <= q))),
          ("F_agreement",toJson (agreement f.S f.T F)),("Fprime_agreement",toJson (agreement f.S f.T Fp)),
          ("no_larger",toJson (decide (Fp.length <= F.length))),
          ("Fprime_refines_P",toJson (refinesBool Fp [f.A,f.B,f.C])),
          ("original_F_refines_some_Q",toJson (os.any (fun o => refinesBool F o.partition))),
          ("Fprime_refines_some_Q",toJson (os.any (fun o => refinesBool Fp o.partition)))])
      let guards := Json.mkObj [("proper_P",toJson (partitionCheck (leaves f.S) [f.A,f.B,f.C])),
        ("source_P_disjoint",toJson (pairwiseEmbeddings f.S [f.A,f.B,f.C])),
        ("A_good",toJson (restrictionAgrees f.S f.T f.A)),
        ("C_clear",toJson (disjointVertices (minimalVertices f.C f.T) (minimalVertices f.A f.T) && disjointVertices (minimalVertices f.C f.T) (minimalVertices f.B f.T)))]
      let j := Json.mkObj [("id",toJson f.name),("q",toJson q),("choice",choiceJson f),
        ("guards",guards),("calls",Json.arr calls.toArray),("outputs",Json.arr (os.map outputJson).toArray),
        ("Q_agreement",toJson (os.map (fun o => agreement f.S f.T o.partition))),
        ("known_F_controls",Json.arr fs.toArray),
        ("root_A_regions",toJson (regions f.A f.T [])),("root_B_regions",toJson (regions f.B f.T []))]
      IO.println j.compress
  IO.println ((Json.mkObj [("boundary_only",toJson true),
    ("duplicate_core_refusals",toJson (generate (.node (.leaf 0) (.leaf 0)) (fun _ => 0) 3).refusals),
    ("sibling_order_same",toJson (sameShape (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))))]).compress)
'''
(P/'src/CompiledControls.lean').write_text(source)
(P/'compiled-control-source-freeze-v1.json').write_text(json.dumps({'fixture_sha256':hashlib.sha256((PREP/'fixtures-v1.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'expected_main_fixture_budget_rows':21,'expected_guard_rows':3,'expected_boundary_selector_rows':5,'expected_extra_boundary_row':1,'known_Fs':40,'oracle_role':'explicit known F values in correctness-test bridge only; runtime goodPairOutputs has no F input','created_before_execution':True},indent=2)+'\n')
print('Compiled control source frozen before execution.')
