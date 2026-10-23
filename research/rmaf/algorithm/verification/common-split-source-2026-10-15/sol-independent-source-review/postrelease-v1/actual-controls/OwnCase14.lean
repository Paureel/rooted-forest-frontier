import OwnReadout
open RMAF OrdinaryCommonSplit Universal233.CoreGraph OwnReadout
namespace OwnCase14
def t : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1009))
def s : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1009)))
def tx : Tree := (.leaf 1009)
def sx : Tree := (.leaf 1009)
def ty : Tree := (.node (.leaf 17) (.leaf 103))
def sy : Tree := (.node (.leaf 17) (.leaf 103))
def mxt : Tree := (.node (.leaf 1000003) (.leaf 1009))
def mxs : Tree := (.node (.leaf 1000003) (.leaf 1009))
def myt : Tree := (.node (.node (.leaf 17) (.leaf 103)) (.leaf 1000033))
def mys : Tree := (.node (.leaf 17) (.node (.leaf 103) (.leaf 1000033)))
def xs : List Nat := [1009]
def ys : List Nat := [17,103]
theorem edge_t : OriginalSplit t xs ys :=
  ⟨[false],(.node (.leaf 17) (.leaf 103)),by decide,by decide,Or.inl (by decide)⟩
theorem edge_s : OriginalSplit s xs ys :=
  ⟨[true,true],(.leaf 1009),by decide,by decide,Or.inr (by decide)⟩
theorem local0 : IsMinimum tx sx 0 := smallCert_minimum _ _ _ (by decide)
theorem local1 : IsMinimum ty sy 0 := smallCert_minimum _ _ _ (by decide)
theorem local2 : IsMinimum mxt mxs 0 := smallCert_minimum _ _ _ (by decide)
theorem local3 : IsMinimum myt mys 1 := smallCert_minimum _ _ _ (by decide)
theorem derived_global : IsMinimum t s 1 := by
  exact common_split_derived_minimum t s tx sx ty sy mxt mxs myt mys xs ys
    1009 17 1000003 1000033 0 0 0 1
    (by decide) (by decide) (by decide) (by decide) edge_t edge_s
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    local0 local1 local2 local3
def readout : Lean.Json := Lean.Json.mkObj [
  ("id",Lean.Json.str "Bswap-arbitrary_Nat_labels"),
  ("restrictions",Lean.Json.arr #[restriction t xs,restriction s xs,restriction t ys,restriction s ys]),
  ("marked",Lean.Json.arr #[markedJson t xs 17 1000003,markedJson s xs 17 1000003,
    markedJson t ys 1009 1000033,markedJson s ys 1009 1000033]),
  ("pairs",Lean.Json.arr #[pairJson t s,pairJson tx sx,pairJson ty sy,pairJson mxt mxs,pairJson myt mys]),
  ("hulls",Lean.toJson (([[[17],[103,1009]],[[17,103],[1009]],[[17,1009],[103]]] : List (List (List Nat))).map fun f =>
     f.map fun b => (minimalVertices b t,minimalVertices b s))),
  ("identity_value",Lean.toJson (commonSplitValue 0 0 0 1))]
end OwnCase14
def main : IO Unit := IO.println OwnCase14.readout.compress
