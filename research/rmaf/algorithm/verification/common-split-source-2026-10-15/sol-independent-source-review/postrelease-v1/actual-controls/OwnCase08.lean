import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase08
def t : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.node (.leaf 1009) (.leaf 10007)))
def s : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.node (.leaf 1009) (.leaf 10007)))
def tx : Tree := (.node (.leaf 17) (.leaf 103))
def sx : Tree := (.node (.leaf 17) (.leaf 103))
def ty : Tree := (.node (.leaf 1009) (.leaf 10007))
def sy : Tree := (.node (.leaf 1009) (.leaf 10007))
def mxt : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000003))
def mxs : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000003))
def myt : Tree := (.node (.leaf 1000033) (.node (.leaf 1009) (.leaf 10007)))
def mys : Tree := (.node (.leaf 1000033) (.node (.leaf 1009) (.leaf 10007)))
def xs : List Nat := [17,103]
def ys : List Nat := [1009,10007]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 0 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 0 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    17 1009 1000003 1000033 0 0 0 0
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "A-arbitrary_Nat_labels"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 1009 1000003,markedJson s xs 1009 1000003,
    markedJson t ys 17 1000033,markedJson s ys 17 1000033]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[17,103,1009,10007]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 0 0))]
end OwnCase08
def main : IO Unit := IO.println OwnCase08.readout.compress
