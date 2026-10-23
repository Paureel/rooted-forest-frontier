import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase19
def t : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 3))
def s : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 3))
def tx : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def sx : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def ty : Tree := (.leaf 3)
def sy : Tree := (.leaf 3)
def mxt : Tree := (.node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.leaf 100))
def mxs : Tree := (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.leaf 3))
def mys : Tree := (.node (.leaf 101) (.leaf 3))
def xs : List Nat := [0,1,2]
def ys : List Nat := [3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.node (.leaf 1) (.leaf 2))),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 1 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 3 100 101 1 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "D-reverse_inputs"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 3 100,markedJson s xs 3 100,
    markedJson t ys 0 101,markedJson s ys 0 101]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[0],[1,2,3]],[[0,1,3],[2]],[[0,2,3],[1]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 1 0 1 0))]
end OwnCase19
def main : IO Unit := IO.println OwnCase19.readout.compress
