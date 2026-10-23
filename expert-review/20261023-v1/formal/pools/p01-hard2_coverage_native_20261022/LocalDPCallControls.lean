-- Literal local-DP offset control before call-site proof construction.
import Hard2PaymentV2
import ExactMinimum
open RMAF ForestState ForestGroups
namespace ContactedHard2DP

def offsetTarget : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def offsetSources : List Tree := [.node (.leaf 0) (.leaf 1),.node (.leaf 2) (.leaf 3)]
theorem positive_offset_control : AllGoodDP.allGood (some offsetTarget) offsetSources=true ∧
 additionalCost offsetSources (AllGoodDP.candidate (some offsetTarget) offsetSources)=1 := by decide
end ContactedHard2DP
#check ContactedClade.restrict_ext
#check ContactedClade.restrict_subset
#check FreshResidual.restriction_materialized
#check FreshResidual.materialized_restriction
#check ForestGroups.local_proper
#check RestrictionBridge.checked_concat
#check AllGoodDP.run_total_exact

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2DP.positive_offset_control
#print axioms ContactedHard2DP.positive_offset_control
