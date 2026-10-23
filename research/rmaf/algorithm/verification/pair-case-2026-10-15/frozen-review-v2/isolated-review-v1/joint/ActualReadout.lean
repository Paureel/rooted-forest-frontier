import Interface
import Lean
namespace FreshActualReadout
open RMAF BinaryExchange PairGeometry Lean
def jn (xs : List Nat) : Json := Json.arr ((xs.map toJson).toArray)
def jp (p : List (List Nat)) : Json := Json.arr ((p.map jn).toArray)
def addr (v : RMAF.Vertex) : String := String.ofList (v.map (fun b => if b then '1' else '0'))
def jv (v : RMAF.Vertex) : Json := Json.str (addr v)
def je (e : RMAF.Vertex × RMAF.Vertex) : Json := Json.arr #[jv e.1,jv e.2]
def jc : Option Choice → Json
  | none => Json.null
  | some (.vertex v) => Json.mkObj [("kind",Json.str "vertex"),("v",jv v)]
  | some (.edge e) => Json.mkObj [("kind",Json.str "edge"),("u",jv e.1),("v",jv e.2)]
def subsets : List Nat → List (List Nat)
  | [] => [[]]
  | x::xs => let ss := subsets xs; ss ++ ss.map (x::·)
def colors : List Nat → List (List Nat × List Nat)
  | [] => [([],[])]
  | x::xs => (colors xs).flatMap (fun (a,b) => [(a,b),(x::a,b),(a,x::b)])
def refineB (F P : List (List Nat)) : Bool := F.all (fun C => P.any (inside C ·))
def treeRows (t : Tree) (labels : List Nat) : Json :=
  Json.mkObj [
    ("hulls",Json.arr (((subsets labels).map (fun a =>
      Json.mkObj [("selection",jn a),("hull",Json.arr (((minimalVertices a t).map jv).toArray)),
        ("regions_degree",Json.arr (((minimalVertices a t).map (fun v =>
          Json.arr #[jv v,toJson ((VertexGeometry.regions a t v).length),toJson (hullDegree t a v)])).toArray))])).toArray)),
    ("choices",Json.arr (((colors labels).map (fun (a,b) =>
      Json.mkObj [("A",jn a),("B",jn b),("choice",jc (choose t a b))])).toArray))]
def exchangeRows (s t : Tree) (A B : List Nat) (P : List (List Nat))
    (ps : List (List (List Nat))) : Json :=
  Json.arr ((((edges t).filter (edgeOK t A B)).flatMap (fun e =>
    match treeAt t e.2 with
    | none => [Json.mkObj [("missing_treeAt",je e)]]
    | some u =>
      ((ps.filter (fun F => agreement s t F && refineB F P)).map (fun F =>
        let fp := exchange A B F u
        let q := (leaves u).contains
        Json.mkObj [("edge",je e),("D",jn (leaves u)),("F",jp F),("Fprime",jp fp),
          ("actual_agreement",toJson (agreement s t fp)),("refines_P",toJson (refineB fp P)),
          ("A_count",toJson (fp.count A)),("nonincreasing",toJson (decide (fp.length <= F.length))),
          ("outside_equal",toJson (outside A B fp == outside A B F)),
          ("B_mono",toJson (fp.all (fun C => !inside C B || (C.all q || C.all (fun x => !q x)))))])))).toArray)
def fixtureRows (name : String) (s t : Tree) (labels A B : List Nat)
    (P : List (List Nat)) (ps : List (List (List Nat))) : Json :=
  Json.mkObj [("fixture",Json.str name),("S",treeRows s labels),("T",treeRows t labels),
    ("partitions",Json.arr ((ps.map (fun F => Json.mkObj [("F",jp F),("agreement",toJson (agreement s t F))])).toArray)),
    ("exchanges",exchangeRows s t A B P ps)]
end FreshActualReadout
