import SelectorControls
import SelectorWork
namespace Universal233.Rule5PaidSelector.Controls
open RMAF ForestState Rule5Case322 Rule5Local Rule5Local.Pre Case322PaidGuard
set_option maxRecDepth 24000
set_option maxHeartbeats 800000
example : (buildSelected sixT sixS 0 1).map (fun R => (requests R.geometry 3).all (fun Q =>
 ForestState.proper (some Q.target) Q.sources &&
 decide (Q.residual=3-Q.branch.originalCuts.length) &&
 decide (Q.sources.length=Q.branch.originalCuts.length+1)))=some true := by decide
example : (buildSelected sixT sixS 0 1).map (fun R => (requests R.geometry 0).isEmpty)=some true := by decide
example : (buildSelected sixT sixS 0 1).map (fun R => (requests R.geometry 1).map PaidRequest.residual)=some [0] := by decide
example : (buildSelected sixT sixS 0 1).map (fun R => (requests R.geometry 1).map (fun Q => Q.sources.length))=some [2] := by decide
end Universal233.Rule5PaidSelector.Controls
