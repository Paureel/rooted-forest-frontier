import FullSourceControls
namespace OrdinaryDispatch.FullSourceWork.Controls
open RMAF ForestState Universal233
example : (agreementMeter (.leaf 0) (.leaf 0) [[0],[0]]).value=true := by cbv;decide
example : budgetTreeWork 1 WorkRecursion.Controls.commonT WorkRecursion.Controls.commonS=2 := by
 rw [weighted_common_literal.2]
 cbv
 decide
end OrdinaryDispatch.FullSourceWork.Controls
