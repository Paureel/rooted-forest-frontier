import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase01
def t : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
def s : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 2)))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.leaf 2)
def sy : Tree := (.leaf 2)
def mxt : Tree := (.node (.node (.leaf 0) (.leaf 1)) (.leaf 100))
def mxs : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def myt : Tree := (.node (.leaf 101) (.leaf 2))
def mys : Tree := (.node (.leaf 101) (.leaf 2))
def xs : List Nat := [0,1]
def ys : List Nat := [2]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 2),by decide,by decide,Or.inl (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "B"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 2 100,markedJson s xs 2 100,
    markedJson t ys 0 101,markedJson s ys 0 101]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[0],[1,2]],[[0,1],[2]],[[0,2],[1]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 1 0))]
end OwnCase01
def main : IO Unit := IO.println OwnCase01.readout.compress
