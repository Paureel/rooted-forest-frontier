import PaidChildren
namespace OrdinaryDispatch.Controls
open RMAF Universal233.CherryBranching

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def noOrdinary : Tree → Tree → Nat → Option Forest := fun _ _ _ => none

theorem actual_paid_child_found :
    (runChildren noOrdinary T S 2 [singletonChild S 0]).map
      (fun F => (agreement T S F,F.length)) = some (true,3) := by cbv

theorem unpaid_child_refused : runChildren noOrdinary T S 1 [singletonChild S 0] = none := by cbv

theorem omitted_cover_refused : runChildren noOrdinary T S 2 [] = none := by decide
end OrdinaryDispatch.Controls
