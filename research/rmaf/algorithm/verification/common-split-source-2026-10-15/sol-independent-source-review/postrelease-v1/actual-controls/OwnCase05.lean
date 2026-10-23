import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase05
def t : Tree := (.node (.leaf 8) (.leaf 10000))
def s : Tree := (.node (.leaf 8) (.leaf 10000))
def tx : Tree := (.leaf 8)
def sx : Tree := (.leaf 8)
def ty : Tree := (.leaf 10000)
def sy : Tree := (.leaf 10000)
def mxt : Tree := (.node (.leaf 8) (.leaf 1000003))
def mxs : Tree := (.node (.leaf 8) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.leaf 10000))
def mys : Tree := (.node (.leaf 1000033) (.leaf 10000))
def xs : List Nat := [8]
def ys : List Nat := [10000]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 8),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    8 10000 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "E"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 10000 1000003,markedJson s xs 10000 1000003,
    markedJson t ys 8 1000033,markedJson s ys 8 1000033]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[8,10000]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 0 0))]
end OwnCase05
def main : IO Unit := IO.println OwnCase05.readout.compress
