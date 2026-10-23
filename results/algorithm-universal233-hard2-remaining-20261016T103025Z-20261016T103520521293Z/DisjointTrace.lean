import TraceProgress
namespace OrdinaryDispatch.Hard2Trace
open RMAF ForestState RestrictionBridge Universal233 Universal233.BothBad
open Universal233.CherryBranching Universal233.Hard2Overlap Universal233.PaidAssembly
open OrdinaryDispatch.Hard2Dispatcher

/-- This record supplies exactly the answer and actual calls of the frozen
disjoint handler; it does not substitute a different source query. -/
def disjointExecution (actual : Ordinary) (T S : Tree) (a b q : Nat) : Execution :=
 Hard2Combine.combine actual T S a b q (DisjointParents.query actual T S (pendantPartition S a b) q)

theorem disjointExecution_answer (actual : Ordinary) (T S : Tree) (a b q : Nat) :
 (disjointExecution actual T S a b q).answer=DisjointParents.run actual T S a b q := rfl

theorem disjointExecution_mass (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat)
 (proper : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (notAll : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notTwo : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2)
 (b : Rat) (base : 2≤b) (upper : b≤3) :
 traceMass b q (disjointExecution actual T S c.a c.b q).calls≤2*b^(-1 : Int)+4*b^(-4 : Int) := by
 obtain ⟨p,r,cuts,hcuts,graph,hp,es,partEq⟩ := actual_source_inputs proper hard
 have three : (pendantPartition S c.a c.b).length=3 := by rw [partEq];rfl
 have bad := DisjointParents.actual_other_disjoint_bad T S _ three notAll notTwo
 have paid := DisjointParents.query_mass actual T S _ q three bad b base
 have total := Rat.le_trans paid (inverse_three_bound b base upper)
 exact Hard2Combine.combine_mass actual T S c.a c.b q _ b base _ total

theorem disjointExecution_strict (actual : Ordinary) {T S : Tree} {c : Candidate} (q : Nat)
 (proper : DepthOne.proper T S=true) (hard : CherryBranching.select T S=some (.hard2,c))
 (call : Call) (mem : call∈(disjointExecution actual T S c.a c.b q).calls) : call.budget<q := by
 obtain ⟨p,r,cuts,hcuts,graph,hp,es,partEq⟩ := actual_source_inputs proper hard
 have three : (pendantPartition S c.a c.b).length=3 := by rw [partEq];rfl
 change call∈Hard2Combine.unitCalls S T c.a c.b q++(DisjointParents.query actual T S (pendantPartition S c.a c.b) q).calls at mem
 rcases List.mem_append.1 mem with unit|paid
 · exact Hard2Combine.unitCalls_strict T S c.a c.b q call unit
 · exact DisjointParents.query_calls_decrease actual T S _ q (by rw [three];decide) call paid
end OrdinaryDispatch.Hard2Trace
