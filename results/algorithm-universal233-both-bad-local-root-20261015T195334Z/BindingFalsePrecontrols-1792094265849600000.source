import BindingPrecontrols
namespace Universal233.BothBadLocal.Controls
open RMAF BothBad BothBad.Precontrols
set_option maxRecDepth 10000
example : budgets (plan S T A B C (PairGeometry.descendants T edge.2) 5)=[3,1,1] := by decide
example : ((solvePair DispatchControls.planted S T A B C edge 5).calls.map Call.budget)=[2,2,2] := by decide
example : plan S T A B C (PairGeometry.descendants T edge.2) 2≠[] := by decide
example : GenericForest.solve malformedActual (some (.leaf 0)) [.leaf 1] 0=some [[999]] := by
 rw [GenericForest.solve.eq_def]
 decide
end Universal233.BothBadLocal.Controls
