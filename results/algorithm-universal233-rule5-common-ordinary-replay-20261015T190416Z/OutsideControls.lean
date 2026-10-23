import OutsideDefs
import PaidControls
namespace OrdinaryCommonSplit.Caller.OutsideControls
open RMAF Universal233 OrdinaryCommonSplit.Controls
open PaidControls
theorem actual_outside_pretest : (outsideReply d FY).isSome=true ∧ replyCost (outsideReply d FY)=some 1 := by decide
theorem literal_extension_cost_two : agreement d.myT d.myS (outsideExtension d FY)=true ∧
    (outsideExtension d FY).length-1=2 := by decide
theorem outside_bound_run : replyCost (runWithOutside d 2 FY cb)=some 2 ∧ runWithOutside d 1 FY cb=none := by decide
theorem actual_rejection_model : DepthOne.pretest01 highMarkedT highMarkedS=.rejected ∧
    agreement highMarkedT highMarkedS [[6],[0,1],[2]]=true := by decide
end OrdinaryCommonSplit.Caller.OutsideControls
