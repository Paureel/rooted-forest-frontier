import BothBadPlanBound
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest.CheckCorrespondence OrdinaryDispatch.EarlyLocalWork
/-- Actual planner work alone has the fixed original-q exponential envelope.
This does not assert the unproved grouped execution local polynomial. -/
theorem bothBadPlanMeter_weighted (S T : Tree) (A B C D : List Nat) (q N Q : Nat)
 (tn:treeNodes T≤N) (sn:treeNodes S≤N) (al:A.length≤N) (bl:B.length≤N) (dl:D.length≤N)
 (budget:q≤Q) :
 ((bothBadPlanMeter S T A B C D q).work:Rat)≤
 ((2*bothBadPlanCoefficient N Q+6:Nat):Rat)*Rule5ActualTrace.base^q:=by
 have h:=bothBadPlanMeter_bound S T A B C D q N Q tn sn al bl dl budget
 have hn:(bothBadPlanMeter S T A B C D q).work≤bothBadPlanCoefficient N Q*2^(q+1)+6:=by omega
 exact Rat.le_trans (Rat.natCast_le_natCast.2 hn) (binary_prefix_absorb _ q)
end OrdinaryDispatch.Hard2SourceWork
