import FamilyTransport
import RestrictionDefs
open TripleDP TripleDP.CostRoute TripleDP.Family

theorem clean_left_label : LeafAt (.node (.leaf 7) (.leaf 9)) [false] 7 := by
  change [] = ([] : Address) ∧ 7 = 7
  decide
theorem clean_closed_support (F : RawFamily t k) (hn : F.openRegion = none)
    (i : Fin k) (a : Address) : (toClosedAssembly F hn).support i a ↔ F.closed i a := Iff.rfl
theorem clean_open_support (F : RawFamily t k) (R : Support)
    (hR : F.openRegion = some R) (hl : HasLeaf t R) (a : Address) :
    (toOpenAssembly F R hR hl).support (.inr ()) a ↔ R a := Iff.rfl

#print axioms clean_left_label
#print axioms clean_closed_support
#print axioms clean_open_support
