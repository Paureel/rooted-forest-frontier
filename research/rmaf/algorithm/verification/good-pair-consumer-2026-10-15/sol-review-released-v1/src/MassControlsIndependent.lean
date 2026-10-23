import Lean
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
{ name := "root-supplied-six-leaf-vertex", S := (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.leaf 3) (.leaf 4))) (.leaf 5)), T := (.node (.node (.node (.leaf 0) (.leaf 3)) (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))) (.leaf 5)), A := [0, 1, 2], B := [3, 4], C := [5], qmax := 5, knownFs := [[[0], [1], [2], [3], [4], [5]], [[0], [1], [2], [3, 4], [5]], [[0, 1], [2], [3], [4], [5]], [[1], [0, 2], [3], [4], [5]], [[0], [1, 2], [3], [4], [5]], [[0, 1, 2], [3], [4], [5]]] },
{ name := "public-good-A-edge-reused", S := (.node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)), T := (.node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 4))) (.node (.leaf 2) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)), A := [1, 2], B := [3, 4, 5, 6], C := [7], qmax := 6, knownFs := [[[1], [2], [3], [4], [5], [6], [7]], [[1], [2], [3, 4], [5], [6], [7]], [[1], [2], [4], [3, 5], [6], [7]], [[1], [2], [4], [5], [3, 6], [7]], [[1], [2], [3], [4, 5], [6], [7]], [[1], [2], [3], [5], [4, 6], [7]], [[1], [2], [3], [4], [5, 6], [7]], [[1, 2], [3], [4], [5], [6], [7]], [[1, 2], [3, 4], [5], [6], [7]], [[1, 2], [3], [4], [5, 6], [7]]] },
{ name := "vertex-good-A-bad-C-not-all-Q-agreement", S := (.node (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.leaf 3) (.leaf 4))) (.node (.node (.leaf 5) (.leaf 6)) (.leaf 7))), T := (.node (.node (.node (.leaf 0) (.leaf 3)) (.node (.leaf 1) (.node (.leaf 2) (.leaf 4)))) (.node (.node (.leaf 5) (.leaf 7)) (.leaf 6))), A := [0, 1, 2], B := [3, 4], C := [5, 6, 7], qmax := 7, knownFs := [[[0], [1], [2], [3], [4], [5], [6], [7]], [[0], [1], [2], [3], [4], [5, 6], [7]], [[0], [1], [2], [3], [4], [6], [5, 7]], [[0], [1], [2], [3], [4], [5], [6, 7]], [[0], [1], [2], [3, 4], [5], [6], [7]], [[0], [1], [2], [3, 4], [5, 6], [7]], [[0], [1], [2], [3, 4], [6], [5, 7]], [[0], [1], [2], [3, 4], [5], [6, 7]], [[0, 1], [2], [3], [4], [5], [6], [7]], [[0, 1], [2], [3], [4], [5, 6], [7]], [[0, 1], [2], [3], [4], [6], [5, 7]], [[0, 1], [2], [3], [4], [5], [6, 7]], [[1], [0, 2], [3], [4], [5], [6], [7]], [[1], [0, 2], [3], [4], [5, 6], [7]], [[1], [0, 2], [3], [4], [6], [5, 7]], [[1], [0, 2], [3], [4], [5], [6, 7]], [[0], [1, 2], [3], [4], [5], [6], [7]], [[0], [1, 2], [3], [4], [5, 6], [7]], [[0], [1, 2], [3], [4], [6], [5, 7]], [[0], [1, 2], [3], [4], [5], [6, 7]], [[0, 1, 2], [3], [4], [5], [6], [7]], [[0, 1, 2], [3], [4], [5, 6], [7]], [[0, 1, 2], [3], [4], [6], [5, 7]], [[0, 1, 2], [3], [4], [5], [6, 7]]] },
{ name := "source-disjointness-only-removed", S := (.node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 5))) (.node (.leaf 2) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)), T := (.node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 4))) (.node (.leaf 2) (.node (.leaf 5) (.leaf 6)))) (.leaf 7)), A := [1, 2], B := [3, 4, 5, 6], C := [7], qmax := 0, knownFs := [] },
{ name := "A-agreement-only-removed-X0-reused", S := (.node (.node (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7))))) (.leaf 3)) (.leaf 8)), T := (.node (.node (.node (.leaf 1) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 6) (.leaf 7)))) (.leaf 8)), A := [1, 2, 3], B := [4, 5, 6, 7], C := [8], qmax := 0, knownFs := [] },
{ name := "other-parent-clearance-only-removed", S := (.node (.node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)) (.leaf 8)), T := (.node (.node (.node (.leaf 1) (.node (.leaf 3) (.leaf 4))) (.node (.leaf 2) (.node (.node (.leaf 5) (.leaf 7)) (.leaf 6)))) (.leaf 8)), A := [1, 2], B := [3, 4, 5, 6], C := [7, 8], qmax := 0, knownFs := [] },
{ name := "singleton-empty-B", S := (.leaf 0), T := (.leaf 0), A := [0], B := [], C := [], qmax := 0, knownFs := [] },
{ name := "absent-B-label", S := (.node (.leaf 0) (.leaf 1)), T := (.node (.leaf 0) (.leaf 1)), A := [0], B := [99], C := [], qmax := 0, knownFs := [] },
{ name := "duplicate-A-label", S := (.node (.leaf 0) (.leaf 1)), T := (.node (.leaf 0) (.leaf 1)), A := [0, 0], B := [1], C := [], qmax := 0, knownFs := [] },
{ name := "overlapping-A-B", S := (.node (.leaf 0) (.leaf 1)), T := (.node (.leaf 0) (.leaf 1)), A := [0], B := [0], C := [], qmax := 0, knownFs := [] },
{ name := "duplicate-target-label", S := (.node (.leaf 0) (.leaf 0)), T := (.node (.leaf 0) (.leaf 0)), A := [0], B := [1], C := [], qmax := 0, knownFs := [] }
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

def controlMain : IO Unit := do
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

def ratJson (r : Rat) : Json := Json.mkObj [("num",toJson r.num),("den",toJson r.den)]
def main : IO Unit := do
  for f in fixtures do
    if !f.knownFs.isEmpty then
      for q in List.range (f.qmax+1) do
        let os := goodPairOutputs f.S f.T f.A f.B q
        for c in ([2,(233:Rat)/100,3] : List Rat) do
          let mass := Universal233.SourceCoverage.rawQMass c os
          let bound := match PairGeometry.choose f.T f.A f.B with
            | some (.edge _) => c^(-3 : Int)
            | _ => c^(-3 : Int)+c^(-4 : Int)
          IO.println ((Json.mkObj [("id",toJson f.name),("q",toJson q),("c",ratJson c),
            ("mass",ratJson mass),("bound",ratJson bound),("le_bound",toJson (decide (mass<=bound)))]).compress)
  match fixtures with
  | f :: _ =>
    let os := goodPairOutputs f.S f.T f.A f.B f.qmax
    let dup := match os with
      | _ :: b :: _ => os ++ [b]
      | _ => []
    let clean := Universal233.SourceCoverage.rawQMass 2 os
    let bad := Universal233.SourceCoverage.rawQMass 2 dup
    IO.println ((Json.mkObj [("duplicate_control",toJson true),("clean_mass",ratJson clean),
      ("duplicate_mass",ratJson bad),("false_dedup_bound_rejected",toJson (decide (bad>clean)))]).compress)
  | [] => pure ()
