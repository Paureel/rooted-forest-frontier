/- Frozen clean controls for source-native local correctness integration. -/
import ControlFlowV4
open RMAF Universal233 OrdinaryDispatch IndependentReconstruction
namespace LocalNativeControls
example : QueryExact (.leaf 0) (.leaf 0) 0 (some [[0]]) := positive_control
example : ¬ QueryExact (.leaf 0) (.leaf 0) 0 none := false_negative_refuted
example (q : Nat) (T S : Tree) : OwnPaid q T S q = none := by simp [OwnPaid]
end LocalNativeControls
