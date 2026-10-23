import EarlyControls
namespace OrdinaryDispatch.FastOrdinary.Controls
open RMAF ForestState Universal233 Rule5Local.Pre
def sixAF : CommonForest := [[0,1],[2],[14,15],[16]]
theorem planted_hard2_agreement : agreement sixT sixS sixAF=true := by decide
theorem planted_hard2_cost : sixAF.length-1=3 := by decide
end OrdinaryDispatch.FastOrdinary.Controls
