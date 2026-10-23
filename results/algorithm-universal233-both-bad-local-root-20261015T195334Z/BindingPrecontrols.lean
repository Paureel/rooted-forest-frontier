import DispatchControls
import LocalExact
namespace Universal233.BothBadLocal.Controls
open RMAF BothBad BothBad.Precontrols
set_option maxRecDepth 10000
def edge : RMAF.Vertex × RMAF.Vertex := ([false],[false,false])
def malformedActual (_ _ : Tree) (_ : Nat) : Option Forest := some [[999]]
theorem literal_edge : PairGeometry.choose T A B=some (.edge edge) := by decide
theorem literal_plan : budgets (plan S T A B C (PairGeometry.descendants T edge.2) 5)=[2,0,0] := by decide
theorem literal_calls : ((solvePair DispatchControls.planted S T A B C edge 5).calls.map Call.budget)=[2,0,0] := by decide
theorem literal_low_plan : plan S T A B C (PairGeometry.descendants T edge.2) 2=[] := by decide
theorem literal_min_plan : budgets (plan S T A B C (PairGeometry.descendants T edge.2) 3)=[0] := by decide
theorem malformed_callback_preserved : malformedActual (.leaf 0) (.leaf 1) 0=some [[999]] := by decide
theorem malformed_forest_refused : GenericForest.solve malformedActual (some (.leaf 0)) [.leaf 1] 0=none := by
 rw [GenericForest.solve.eq_def]
 decide
end Universal233.BothBadLocal.Controls
