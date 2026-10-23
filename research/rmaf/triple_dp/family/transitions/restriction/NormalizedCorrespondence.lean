import FourTransitions
import NormalizedRestriction

namespace TripleDP.Transitions.Restriction
open TripleDP.Family TripleDP.CostRoute

variable {α : Type} {l r : BTree α} {k : Nat}

theorem normalized_closed_four (F : RawFamily (.node l r) k)
    (hn : (normalize F).openRegion = none) :
    FourRecovery (toClosedAssembly (normalize F) hn)
      (NormalizedRoute.normalized_closed_openBranchLive F hn) :=
  four_transition_recovery _ _

theorem normalized_open_four (F : RawFamily (.node l r) k) (R : Support)
    (hR : (normalize F).openRegion = some R) (hl : HasLeaf (.node l r) R) :
    FourRecovery (toOpenAssembly (normalize F) R hR hl)
      (NormalizedRoute.normalized_open_openBranchLive F R hR hl) :=
  four_transition_recovery _ _

theorem normalized_closed_child_support (F : RawFamily (.node l r) k)
    (hn : (normalize F).openRegion = none) (side : Bool)
    (i : LiveIndex (toClosedAssembly (normalize F) hn) side) :
    (restrict (toClosedAssembly (normalize F) hn)
      (NormalizedRoute.normalized_closed_openBranchLive F hn) side).support i =
      fun a => (normalize F).closed i.val (side :: a) := rfl

theorem normalized_open_child_support (F : RawFamily (.node l r) k) (R : Support)
    (hR : (normalize F).openRegion = some R) (hl : HasLeaf (.node l r) R) (side : Bool)
    (i : LiveIndex (toOpenAssembly (normalize F) R hR hl) side) :
    (restrict (toOpenAssembly (normalize F) R hR hl)
      (NormalizedRoute.normalized_open_openBranchLive F R hR hl) side).support i =
      fun a => openIndexedSupport (normalize F) R i.val (side :: a) := rfl

#print axioms normalized_closed_four
#print axioms normalized_open_four
#print axioms normalized_closed_child_support
#print axioms normalized_open_child_support
end TripleDP.Transitions.Restriction
