"""One-shot postcontact Lean runtime readout generator from frozen fixtures.
Reads no author controls. Finite tables are frozen independent partitions.
"""
import argparse,json,pathlib,sys
H=pathlib.Path(__file__).resolve().parent;PRE=H.parent
sys.path.insert(0,str(PRE));import original_graph as og
def tree(t):return f"(.leaf {t})"if type(t)is int else f"(.node {tree(t[0])} {tree(t[1])})"
def natlist(xs):return"["+",".join(str(x)for x in xs)+"]"
def forest(F):return"["+",".join(natlist(b)for b in F)+"]"
def main():
    parser=argparse.ArgumentParser();parser.add_argument("--limit",type=int,default=5);parser.add_argument("--output",default="RuntimeReadout.lean");args=parser.parse_args()
    fixtures=json.loads((PRE/"fixtures-output-v2.json").read_text())["fixtures"][:args.limit]
    template=r'''import Rule4Solve
import Lean
open RMAF Lean Universal233.Rule4
def tj : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[tj l,tj r]
def cj (cuts : List RMAF.Vertex) : Json :=
  toJson (cuts.map (fun p => String.ofList (p.map (fun s => if s then '1' else '0'))))
def fj (F : Option (List (List Nat))) : Json := match F with
  | none => Json.null
  | some F => toJson F
def bj (b : Branch) : Json := Json.mkObj [
  ("target",tj b.target),("source",tj b.source),("cuts",cj b.cuts),
  ("partition",toJson b.partition),("source_forest",Json.arr (b.sourceForest.map tj).toArray),
  ("cost",toJson b.cost),("swapped",toJson b.swapped),
  ("proper",toJson (ForestState.proper (some b.target) b.sourceForest))]
def quietChild (allF : List (List (List Nat))) (b : Branch) (r : Nat) :=
  RMAF.best List.length (fun F => ForestState.agrees (some b.target) b.sourceForest F &&
    decide (ForestState.additionalCost b.sourceForest F ≤ r)) allF
def child (tag : String) (q : Nat) (allF : List (List (List Nat))) (b : Branch) (r : Nat) :=
  dbg_trace ("CALL " ++ (Json.mkObj [("fixture",toJson tag),("parent_q",toJson q),
    ("branch",bj b),("residual",toJson r)]).compress)
  quietChild allF b r
def recoveryJ (o : Option Universal233.CoreProgram.Output) : Json := match o with
  | none => Json.null
  | some o => Json.mkObj [("partition",toJson o.partition),("cuts",cj o.sourceCuts)]
def runFixture (tag : String) (T S : Tree) (allP allF : List (List (List Nat))) : Json :=
  match select T S with
  | none => Json.mkObj [("fixture",toJson tag),("selected",toJson false)]
  | some s =>
    let states := (branches s).map (fun b => Json.mkObj [("branch",bj b),
      ("table",toJson (allP.filter (fun F => ForestState.agrees (some b.target) b.sourceForest F)))])
    let budgets := (List.range 5).map (fun q =>
      let solve := solveForest s q (child tag q allF)
      let cuts := solveCuts s q (child tag q allF)
      Json.mkObj [("q",toJson q),("solveForest",fj solve),("solveCuts",recoveryJ cuts),
        ("affordable",Json.arr ((branches s).filter (fun b => b.cost ≤ q) |>.map (fun b =>
          Json.mkObj [("branch",bj b),("residual",toJson (q-b.cost))])).toArray),
        ("masses",toJson ([2,(233/100 : Rat),3].map (fun c => toString (callbackMass c q ((branches s).map Branch.cost)))))])
    Json.mkObj [("fixture",toJson tag),("selected",toJson true),("a",toJson s.raw.a),
      ("b",toJson s.raw.b),("c",toJson s.raw.c),("states",toJson states),("budgets",toJson budgets)]
def guardJ (tag : String) (T S : Tree) := Json.mkObj [("guard",toJson tag),
  ("selected",toJson (select T S |>.isSome)),
  ("proper_T",toJson (decide (leaves T).Nodup)),
  ("proper_S",toJson (decide (leaves S).Nodup)),
  ("labels_perm",toJson (decide ((leaves T).Perm (leaves S)))),
  ("no_common",toJson ((orderedCherries T).all (fun p => !(orderedCherries S).contains p))),
  ("no_t1_target",toJson ((orderedCherries T).all (fun p => (Universal233.HardParent.pendantOriginal S p.1 p.2).length != 1))),
  ("no_t1_source",toJson ((orderedCherries S).all (fun p => (Universal233.HardParent.pendantOriginal T p.1 p.2).length != 1))),
  ("local_admissions",toJson ((rawChoices T S).filter (fun s => decide (LocalGuard T S s))).length)]
'''
    lines=[template]
    for i,f in enumerate(fixtures):
        allP=list(og.partitions(sorted(og.Graph(f["T"]).labels)))
        lines.append(f"def fixture{i} : Json := runFixture {json.dumps(f['name'])} {tree(f['T'])} {tree(f['S'])} [{','.join(forest(F)for F in allP)}] [{','.join(forest(F)for F in f['agreements'])}]\n")
    guards=[("common",[[[0,1],3],[2,4]],[[[0,1],3],[2,4]]),
      ("t1-forward",[[0,1],[2,3]],[[[0,2],1],3]),("t1-source",[[[0,2],1],3],[[0,1],[2,3]]),
      ("unequal",[[[0,1],3],[2,4]],[[0,2],[1,[3,9]]]),
      ("duplicate",[[[0,1],3],[2,4]],[[0,2],[1,[3,3]]]),
      ("bad-geometry",[[[0,1],3],[2,[4,5]]],[[[[[0,2],3],4],1],5])]
    for i,(tag,T,S)in enumerate(guards):lines.append(f"def guard{i} : Json := guardJ {json.dumps(tag)} {tree(T)} {tree(S)}\n")
    lines.append("def main : IO Unit := do\n")
    for i in range(len(fixtures)):lines.append(f'  IO.println ("RESULT " ++ fixture{i}.compress)\n')
    for i in range(len(guards)):lines.append(f'  IO.println ("RESULT " ++ guard{i}.compress)\n')
    (H/args.output).write_text("".join(lines))
    print(json.dumps({"fixtures":len(fixtures),"guards":len(guards),"bytes":(H/args.output).stat().st_size}))
if __name__=="__main__":main()
