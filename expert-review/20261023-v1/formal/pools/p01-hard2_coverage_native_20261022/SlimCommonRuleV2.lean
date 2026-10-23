/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Actual CommonReady from the independent leaf-multiset invariants and explicit
   reused selector/cut-zero structural reflection. CommonLift geometry stays open. -/
import SlimCommonCoreV2
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentCommon

theorem address_to_syntax {T : Tree} {p : RMAF.Vertex} {a b : Nat}
 (hc : CoreGraph.CherryAt T p a b) : HasCherry a b T := by
 induction p generalizing T with
 | nil =>
  simp [CoreGraph.CherryAt,CoreGraph.subtree] at hc
  subst T
  exact .here
 | cons side p ih =>
  cases T with
  | leaf x => simp [CoreGraph.CherryAt,CoreGraph.subtree] at hc
  | node l r =>
   cases side
   · exact .left (ih hc)
   · exact .right (ih hc)

end IndependentCommon

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @IndependentCommon.address_to_syntax
#print axioms IndependentCommon.address_to_syntax
