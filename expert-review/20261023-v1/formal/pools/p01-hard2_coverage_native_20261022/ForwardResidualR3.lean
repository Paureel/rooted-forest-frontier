import EmittedSourceR3
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair ContactedSource
namespace ContactedForward

theorem emitted_original_orientation {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) (F : List (List Nat)) :
 (agreement b.target b.source F=true ∧ VertexGeometry.Refines F b.partition) ↔ OriginalCovered T S b F := by
 simp only [Rule4.branches,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 · exact Iff.rfl
 · exact Iff.rfl
 · exact ⟨fun h=>⟨agreement_swap h.1,h.2⟩,fun h=>⟨agreement_swap h.1,h.2⟩⟩

/- Completed peer bridge is reused; no generic solver theorem is supplied. -/
theorem emitted_materialized_scope {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) :
 b.sourceForest.length=b.partition.length ∧ ForestState.proper (some b.target) b.sourceForest=true ∧
 (∀F,ForestState.agrees (some b.target) b.sourceForest F=true ↔ OriginalCovered T S b F) := by
 have proper := emitted_oriented_proper s b member
 have lit := emitted_literal_checks s b member
 have bridge := FreshResidual.residual_transfer_scope.1
 have base := bridge b.target b.source b.partition [] proper lit.1 lit.2.1
 refine ⟨base.1,base.2.1,?_⟩
 intro F
 exact (bridge b.target b.source b.partition F proper lit.1 lit.2.1).2.2.trans (emitted_original_orientation s member F)

theorem emitted_payment_identity {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) {F : List (List Nat)} (covered : OriginalCovered T S b F) :
 b.cost+additionalCost b.sourceForest F=F.length-1 := by
 have lit := emitted_literal_checks s b member
 have oriented := (emitted_original_orientation s member F).2 covered
 have af := oriented.1
 simp only [agreement,Bool.and_eq_true] at af
 have ns := (IndependentReconstruction.proper_parts (emitted_oriented_proper s b member)).2.1
 have length := IndependentPaid.refinement_length (leaves b.source) F b.partition ns af.1.1.1.2 lit.1 oriented.2
 have sourceCount := (emitted_materialized_scope s member).1
 unfold additionalCost
 rw [sourceCount]
 omega

theorem original_affordable_child {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) {q : Nat} {F : List (List Nat)}
 (covered : OriginalCovered T S b F) (budget : F.length-1≤q) :
 b.cost≤q ∧ Rule4.ChildFeasible b (q-b.cost) F := by
 have identity := emitted_payment_identity s member covered
 have residual : additionalCost b.sourceForest F≤q-b.cost := by omega
 exact ⟨by omega,((emitted_materialized_scope s member).2.2 F).2 covered,residual⟩

theorem child_original_budget {T S : Tree} (s : Rule4.Choice T S) {b : Rule4.Branch}
 (member : b∈Rule4.branches s) {q : Nat} (affordable : b.cost≤q) {F : List (List Nat)}
 (child : Rule4.ChildFeasible b (q-b.cost) F) : agreement T S F=true ∧ F.length-1≤q := by
 have covered := ((emitted_materialized_scope s member).2.2 F).1 child.1
 have identity := emitted_payment_identity s member covered
 exact ⟨covered.1,by have bound := child.2;omega⟩

end ContactedForward

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForward.emitted_original_orientation
#print axioms ContactedForward.emitted_original_orientation
#check @ContactedForward.emitted_materialized_scope
#print axioms ContactedForward.emitted_materialized_scope
#check @ContactedForward.emitted_payment_identity
#print axioms ContactedForward.emitted_payment_identity
#check @ContactedForward.original_affordable_child
#print axioms ContactedForward.original_affordable_child
#check @ContactedForward.child_original_budget
#print axioms ContactedForward.child_original_budget
