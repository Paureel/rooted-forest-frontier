import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase12
def t : Tree := (.node (.leaf 2) (.node (.leaf 1) (.leaf 0)))
def s : Tree := (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def tx : Tree := (.leaf 2)
def sx : Tree := (.leaf 2)
def ty : Tree := (.node (.leaf 1) (.leaf 0))
def sy : Tree := (.node (.leaf 1) (.leaf 0))
def mxt : Tree := (.node (.leaf 2) (.leaf 100))
def mxs : Tree := (.node (.leaf 2) (.leaf 100))
def myt : Tree := (.node (.leaf 101) (.node (.leaf 1) (.leaf 0)))
def mys : Tree := (.node (.node (.leaf 101) (.leaf 1)) (.leaf 0))
def xs : List Nat := [2]
def ys : List Nat := [0,1]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false,false],(.leaf 2),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    2 0 100 101 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "Bswap-child_swaps"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 0 100,markedJson s xs 0 100,
    markedJson t ys 2 101,markedJson s ys 2 101]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[0],[1,2]],[[0,1],[2]],[[0,2],[1]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 0 1))]
end OwnCase12
def main : IO Unit := IO.println OwnCase12.readout.compress
