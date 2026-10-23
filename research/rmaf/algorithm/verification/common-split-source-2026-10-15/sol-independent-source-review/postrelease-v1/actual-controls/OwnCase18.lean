import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase18
def t : Tree := (.node (.leaf 3) (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))
def s : Tree := (.node (.leaf 3) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0)))
def tx : Tree := (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))
def sx : Tree := (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def ty : Tree := (.leaf 3)
def sy : Tree := (.leaf 3)
def mxt : Tree := (.node (.leaf 100) (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))
def mxs : Tree := (.node (.leaf 100) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0)))
def myt : Tree := (.node (.leaf 3) (.leaf 101))
def mys : Tree := (.node (.leaf 3) (.leaf 101))
def xs : List Nat := [0,1,2]
def ys : List Nat := [3]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 3),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 3),by decide,by decide,Or.inl (by decide)⟩
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
  ("id",Lean.Json.str "D-child_swaps"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 3 100,markedJson s xs 3 100,
    markedJson t ys 0 101,markedJson s ys 0 101]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[0],[1,2,3]],[[0,1,3],[2]],[[0,2,3],[1]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 1 0 1 0))]
end OwnCase18
def main : IO Unit := IO.println OwnCase18.readout.compress
