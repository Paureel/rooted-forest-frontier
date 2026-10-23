import Equivalence
import WholeMass
import QueryWork
import Witness01

/-! One-task integration of literal components. No graph or minimum fields. -/
namespace GenericForest
open RMAF RestrictionBridge ForestState OutputState VertexGeometry
open Universal233 CoreProgram PaidQueries
abbrev Forest := List (List Nat)

structure Overlap where
  left : Nat
  right : Nat
  vertex : RMAF.Vertex
  deriving DecidableEq, Repr

def overlap (t : Tree) (ss : List Tree) : Option Overlap :=
  ((ss.zipIdx).flatMap fun a => (ss.zipIdx).filterMap fun b =>
    if a.2 < b.2 then
      ((minimalVertices (leaves a.1) t).find? fun v =>
        (minimalVertices (leaves b.1) t).contains v).map (Overlap.mk a.2 b.2)
    else none).head?

def replace (ss : List Tree) (i : Nat) (Q : Forest) : List Tree :=
  match ss[i]? with
  | none => ss
  | some s => ss.take i ++ sourceForest s Q ++ ss.drop (i+1)

def componentPair (t s : Tree) : Option (Tree × Tree) :=
  (restrict (leaves s) t).map (fun u => (u,s))

def jobs (t : Tree) : List Tree → Option (List (Job (Tree × Tree) Forest))
  | [] => some []
  | s :: ss => (componentPair t s).bind fun p =>
    match DepthOne.pretest01 p.1 p.2 with
    | .refused => none
    | .rejected => (jobs t ss).map (.hard p :: ·)
    | .found c => (jobs t ss).map (.resolved p (DepthOne.cutCost c) (DepthOne.forest s c) :: ·)

def disjointAttempt (t : Tree) (ss : List Tree)
    (ordinary : Tree → Tree → Nat → Option Forest) (q : Nat) : Option (Receipt Forest) :=
  (jobs t ss).map (schedule (fun p b => (ordinary p.1 p.2 b).map (fun F => (F.length-1,F))) q)

def raw (t : Tree) (ss : List Tree) (i : Nat) (v : RMAF.Vertex) (q : Nat) : List Output :=
  match ss[i]? with
  | none => []
  | some s => (generate s (colorLabel t v) q).outputs

end GenericForest
