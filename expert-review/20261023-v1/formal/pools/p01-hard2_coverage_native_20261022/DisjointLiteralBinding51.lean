import DisjointRefiningCover45
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
set_option autoImplicit false
namespace FreshLiteralDisjoint
/-- Every recorded literal singleton call spends one cut before its callback. -/
theorem literal_unit_calls_strict (S T : Tree) (a b q : Nat) :
 ∀call∈Hard2Combine.unitCalls S T a b q,call.budget<q := by
 intro call hc
 by_cases affordable : 1≤q
 · simp [Hard2Combine.unitCalls,remaining,singletonChild,makeChild,affordable] at hc
   rcases hc with rfl | rfl <;> change q-1<q <;> omega
 · simp [Hard2Combine.unitCalls,remaining,singletonChild,makeChild,affordable] at hc

theorem literal_disjoint_combined_answer (actual : DisjointParents.Ordinary)
 (T S : Tree) (a b q : Nat) :
 DisjointParents.run actual T S a b q=
 (Hard2Combine.combine actual T S a b q
   (DisjointParents.query actual T S (pendantPartition S a b) q)).answer := rfl

theorem literal_combined_calls_strict (actual : DisjointParents.Ordinary)
 (T S : Tree) (a b q : Nat) (paid : BothBad.Execution)
 (paidStrict : ∀call∈paid.calls,call.budget<q) :
 ∀call∈(Hard2Combine.combine actual T S a b q paid).calls,call.budget<q := by
 intro call hc
 change call∈Hard2Combine.unitCalls S T a b q++paid.calls at hc
 rcases List.mem_append.mp hc with hu | hp
 · exact literal_unit_calls_strict S T a b q call hu
 · exact paidStrict call hp

theorem actual_mixed_combined_route (actual : DisjointParents.Ordinary) (T S : Tree)
 (c d : Candidate) (q : Nat) (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notRule5 : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 Hard2Dispatcher.run actual T S c d q=
 (Hard2Combine.combine actual T S c.a c.b q
   (DisjointParents.query actual T S (pendantPartition S c.a c.b) q)).answer := by
 exact (actual_disjoint_mixed_route actual T S c d q picked good notRule5).trans
   (literal_disjoint_combined_answer actual T S c.a c.b q)

theorem original_mixed_combined_calls_strict (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 ∀call∈(Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q
   (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q)).calls,
 call.budget<q := by
 exact literal_combined_calls_strict _ T S c.a c.b q _
   (original_parent_query_and_strict q T S c d proper selected picked below).2
end FreshLiteralDisjoint
#print axioms FreshLiteralDisjoint.literal_unit_calls_strict
#print axioms FreshLiteralDisjoint.literal_disjoint_combined_answer
#print axioms FreshLiteralDisjoint.literal_combined_calls_strict
#print axioms FreshLiteralDisjoint.actual_mixed_combined_route
#print axioms FreshLiteralDisjoint.original_mixed_combined_calls_strict

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.literal_unit_calls_strict
#print axioms FreshLiteralDisjoint.literal_unit_calls_strict
#check @FreshLiteralDisjoint.literal_disjoint_combined_answer
#print axioms FreshLiteralDisjoint.literal_disjoint_combined_answer
#check @FreshLiteralDisjoint.literal_combined_calls_strict
#print axioms FreshLiteralDisjoint.literal_combined_calls_strict
#check @FreshLiteralDisjoint.actual_mixed_combined_route
#print axioms FreshLiteralDisjoint.actual_mixed_combined_route
#check @FreshLiteralDisjoint.original_mixed_combined_calls_strict
#print axioms FreshLiteralDisjoint.original_mixed_combined_calls_strict
