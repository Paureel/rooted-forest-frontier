import BothConsumers
import Lean
open Lean RMAF Universal233 CoreProgram BothBad

private def s : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1))
  (.node (.node (.node (.node (.leaf 3) (.leaf 4)) (.leaf 7))
    (.node (.node (.leaf 5) (.leaf 6)) (.leaf 8))) (.node (.leaf 9) (.leaf 10)))
private def t : Tree := .node (.node (.node (.leaf 2)
  (.node (.node (.leaf 0) (.leaf 1)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))))
  (.node (.leaf 7) (.leaf 8))) (.node (.leaf 9) (.leaf 10))
private def p : Forest := [[0,1,2],[3,4,5,6,7,8],[9,10]]
private def f7 : Forest := [[0,1],[2],[3,4],[5],[6],[7,8],[9,10]]
private def f8 : Forest := [[0],[1],[2],[3,4],[5],[6],[7,8],[9,10]]
private def f9 : Forest := [[0],[1],[2],[3],[4],[5],[6],[7,8],[9,10]]
private def entry (b : Nat) : Entry := ⟨⟨p,[[false],[true,false]]⟩,.full,b⟩
@[noinline] private unsafe def logged (ref : IO.Ref (List Nat)) (kind : Nat)
    (_ : Option Tree) (_ : List Tree) (b : Nat) : Option Forest := unsafeBaseIO do
  ref.modify (·++[b])
  return if kind=1 then some p else if kind=2 then some [] else
    some (if b=0 then f8 else if b=1 then f7 else f9)

unsafe def main : IO Unit := do
  let mut rows : Array Json := #[]
  for kind in [0,1,2] do
    let ref ← IO.mkRef ([] : List Nat)
    let r := execute (logged ref kind) t s 10 ([0,1,2,1].map entry)
    let answer := toJson r.answer
    let calls := r.calls.map Call.budget
    let encoded := (Json.mkObj [("answer",answer),("reported",toJson calls)]).compress
    let seen ← ref.get
    rows := rows.push (Json.mkObj [("kind",toJson kind),("result",.str encoded),("observed",toJson seen)])
  let s8 : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1))
    (.node (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4)) (.node (.leaf 6) (.leaf 7)))
  let t8 : Tree := .node (.node (.node (.leaf 2) (.node (.node (.leaf 0) (.leaf 1)) (.leaf 3)))
    (.node (.leaf 4) (.leaf 5))) (.node (.leaf 6) (.leaf 7))
  let overlap : Tree := .node (.node (.leaf 2) (.node (.node (.node (.leaf 0) (.leaf 6)) (.leaf 1))
    (.node (.leaf 3) (.leaf 7)))) (.node (.leaf 4) (.leaf 5))
  let a := [0,1,2]; let b := [3,4,5]; let c := [6,7]
  let choiceCorrect := decide (PairGeometry.choose overlap a b=some (.edge ([false],[false,true])))
  let cClearA := disjointVertices (minimalVertices c overlap) (minimalVertices a overlap)
  let cClearB := disjointVertices (minimalVertices c overlap) (minimalVertices b overlap)
  IO.println (Json.mkObj [("selection",.arr rows),("candidate_lengths",toJson [f8.length,f7.length,f9.length,f7.length]),
    ("source_only_rejected",toJson (decide (checked t8 s8 10 (some [a,b,c])=none))),
    ("C_clearance_boundary",Json.mkObj [("selector_expected",toJson choiceCorrect),
      ("partition",toJson (partitionCheck (leaves s8) [a,b,c])),("source_disjoint",toJson (pairwiseEmbeddings s8 [a,b,c])),
      ("A_bad",toJson (!(restrictionAgrees s8 overlap a))),("B_bad",toJson (!(restrictionAgrees s8 overlap b))),
      ("C_good",toJson (restrictionAgrees s8 overlap c)),("C_clear_A",toJson cClearA),("C_clear_B",toJson cClearB)]),
    ("bad_C_partitions",toJson ([[],[99],[1,6,7]].map fun bad => partitionCheck (leaves s8) [a,b,bad]))]).compress
