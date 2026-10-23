import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase03
def t : Tree := (.node (.leaf 0) (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))))
def s : Tree := (.node (.leaf 2) (.node (.leaf 3) (.node (.leaf 0) (.leaf 1))))
def tx : Tree := (.node (.leaf 0) (.leaf 1))
def sx : Tree := (.node (.leaf 0) (.leaf 1))
def ty : Tree := (.node (.leaf 2) (.leaf 3))
def sy : Tree := (.node (.leaf 2) (.leaf 3))
def mxt : Tree := (.node (.leaf 0) (.node (.leaf 1) (.leaf 100)))
def mxs : Tree := (.node (.leaf 100) (.node (.leaf 0) (.leaf 1)))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 2) (.leaf 3)))
def mys : Tree := (.node (.leaf 2) (.node (.leaf 3) (.leaf 101)))
def xs : List Nat := [0,1]
def ys : List Nat := [2,3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[true,true],(.node (.leaf 2) (.leaf 3)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.node (.leaf 0) (.leaf 1)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 1 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    0 2 100 101 0 0 1 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "C"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 2 100,markedJson s xs 2 100,
    markedJson t ys 0 101,markedJson s ys 0 101]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[0,1],[2,3]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 1 1))]
end OwnCase03
def main : IO Unit := IO.println OwnCase03.readout.compress
