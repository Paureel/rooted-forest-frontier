import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase23
def t : Tree := (.node (.leaf 99991) (.leaf 999983))
def s : Tree := (.node (.leaf 99991) (.leaf 999983))
def tx : Tree := (.leaf 99991)
def sx : Tree := (.leaf 99991)
def ty : Tree := (.leaf 999983)
def sy : Tree := (.leaf 999983)
def mxt : Tree := (.node (.leaf 99991) (.leaf 1000037))
def mxs : Tree := (.node (.leaf 99991) (.leaf 1000037))
def myt : Tree := (.node (.leaf 1000039) (.leaf 999983))
def mys : Tree := (.node (.leaf 1000039) (.leaf 999983))
def xs : List Nat := [99991]
def ys : List Nat := [999983]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.leaf 99991),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.leaf 99991),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    99991 999983 1000037 1000039 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "E-arbitrary_Nat_labels"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 999983 1000037,markedJson s xs 999983 1000037,
    markedJson t ys 99991 1000039,markedJson s ys 99991 1000039]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[99991,999983]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 0 0))]
end OwnCase23
def main : IO Unit := IO.println OwnCase23.readout.compress
