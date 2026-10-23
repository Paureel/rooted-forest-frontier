import DerivedMinimum
import Lean.Data.Json
open RMAF OrdinaryCommonSplit Universal233.DepthOne Universal233.CoreGraph Lean
namespace OwnReadout
def smallCert (t s : Tree) (m : Nat) : Bool :=
  match pretest01 t s with
  | .found c => decide (cutCost c=m)
  | _ => false
theorem smallCert_minimum (t s : Tree) (m : Nat) (h : smallCert t s m=true) :
    IsMinimum t s m := by
  cases e : pretest01 t s with
  | refused => simp [smallCert,e] at h
  | rejected => simp [smallCert,e] at h
  | found c =>
    have eq : cutCost c=m := by simpa [smallCert,e] using h
    obtain ⟨ha,hc,lower⟩ := found_globally_minimum t s c e
    exact ⟨⟨forest s c,ha,hc.trans eq⟩,fun f hf => eq ▸ lower f hf⟩
def jt : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jt l,jt r]
def restriction (t : Tree) (x : List Nat) : Json :=
  match restrict x t with | none => Json.null | some u => jt u
def markedJson (t : Tree) (x : List Nat) (y r : Nat) : Json :=
  match marked t x y r with | none => Json.null | some u => jt u
def finiteAFs (t s : Tree) : List (List (List Nat)) :=
  let labels := leaves t
  ((assignments labels.length labels.length).map fun a =>
    (blocks a).map (fun b => b.map (fun i => labels[i]!))).filter (agreement t s)
def pretestJson (t s : Tree) : Json :=
  match pretest01 t s with
  | .refused => Json.str "refused"
  | .rejected => Json.str "rejected"
  | .found c => Json.mkObj [("cost",toJson (cutCost c)),("forest",toJson (forest s c)),
      ("agreement",toJson (agreement t s (forest s c))),("cut",toJson c)]
def pairJson (t s : Tree) : Json := Json.mkObj [
  ("T",jt t),("S",jt s),("proper",toJson (proper t s)),
  ("pretest",pretestJson t s),("all_af_encodings",toJson (finiteAFs t s))]
end OwnReadout
