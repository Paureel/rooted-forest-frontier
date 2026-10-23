/- Author integration of the saved LocalFacts15 support boundary.
   Source proofs are contacted; no independent reconstruction credit. -/
import LocalFacts15
open RMAF ForestState Universal233 Universal233.CherryBranching OrdinaryDispatch
open OrdinaryDispatch.FastOrdinary
namespace LocalNative

def licensed_support : AuthoredGlobal.LocalSupport :=
 ⟨DepthOne.found_spec, DepthOne.refused_iff, DepthOne.candidate_complete,
  DepthOne.agreement_nonempty, common_pair_ready, common_pair_exact,
  select_none_leaf, leaf_not_rejected⟩

theorem common_ready : IndependentReconstruction.CommonReady := by
 intro T S reverse c hp _ selected
 exact licensed_support.common_ready hp (AuthoredGlobal.common_selected selected)

theorem common_lift : IndependentReconstruction.CommonLift := by
 intro q T S reverse c answer hp _ selected exactness
 exact licensed_support.common_transport hp (AuthoredGlobal.common_selected selected) q answer exactness

theorem reject_impossible : IndependentReconstruction.RejectImpossible := by
 intro T S hp rejected
 exact AuthoredGlobal.early_not_refused licensed_support hp rejected

#print common_ready
#print common_lift
#print reject_impossible
#print axioms common_ready
#print axioms common_lift
#print axioms reject_impossible
end LocalNative
