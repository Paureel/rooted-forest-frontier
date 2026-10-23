/- Maximum checked caller interface; actual residual callback exactness remains explicit. -/
import ReusedCaller
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedRepair ContactedSource
namespace ContactedOneConsumer

theorem literal_singleton_coverage {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.one reverse c) :
 let A := (Oriented reverse T S).1
 let B := (Oriented reverse T S).2
 let children := [pendantChild B c.a c.b]
 IndependentPaid.Literal B children ∧ (∀child∈children,1≤child.paid) ∧
 IndependentPaid.Coverage A B children := by
 have ready := selected_literal_and_coverage proper selected
 refine ⟨?_,?_,?_⟩
 · intro child member
   have eq : child=pendantChild (Oriented reverse T S).2 c.a c.b := by simpa only [List.mem_singleton] using member
   subst child
   exact ⟨ready.1,ready.2.1,ready.2.2.2.1,ready.2.2.1⟩
 · intro child member
   have eq : child=pendantChild (Oriented reverse T S).2 c.a c.b := by simpa only [List.mem_singleton] using member
   subst child
   exact ready.2.2.2.2.1
 · intro F hF
   obtain ⟨H,feas,len⟩ := ready.2.2.2.2.2 F hF
   exact ⟨pendantChild (Oriented reverse T S).2 c.a c.b,List.mem_cons_self,H,feas,len⟩

theorem original_query_oriented {T S : Tree} {q : Nat} {reverse : Bool} {answer : Option CommonForest}
 (h : QueryExact (Oriented reverse T S).1 (Oriented reverse T S).2 q answer) : QueryExact T S q answer := by
 cases reverse
 · exact h
 · cases answer with
   | none => intro F hF;exact h F (IndependentGeometry.agreement_swap hF)
   | some F =>
    refine ⟨IndependentGeometry.agreement_swap h.1,h.2.1,?_⟩
    intro G hG
    exact h.2.2 G (IndependentGeometry.agreement_swap hG)

theorem checked_one_caller (actual : Tree→Tree→Nat→Option Forest) (q : Nat)
 {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (_rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.one reverse c)
 (callback : IndependentPaid.CurrentChildren actual
  (Oriented reverse T S).1 (Oriented reverse T S).2 q [pendantChild (Oriented reverse T S).2 c.a c.b]) :
 QueryExact T S q (runChildren actual (Oriented reverse T S).1 (Oriented reverse T S).2 q
  [pendantChild (Oriented reverse T S).2 c.a c.b]) := by
 have domain := actual_one_domain proper selected
 have sourceND := (IndependentReconstruction.proper_parts domain.1).2.1
 have ready := literal_singleton_coverage proper selected
 apply original_query_oriented (reverse:=reverse)
 exact IndependentPaid.caller_query actual _ _ q _ sourceND ready.1 callback ready.2.2

/- A spelling of the exact remaining callback obligation at this caller.
   No inhabitant is supplied; this is not the generic callback proof. -/
def OneCurrentCallback (actual : Tree→Tree→Nat→Option Forest) (q : Nat) (T S : Tree) : Prop :=
 ∀reverse c,DepthOne.proper T S=true→DepthOne.pretest01 T S=.rejected→early T S=.one reverse c→
 IndependentPaid.CurrentChildren actual (Oriented reverse T S).1 (Oriented reverse T S).2 q
  [pendantChild (Oriented reverse T S).2 c.a c.b]
end ContactedOneConsumer

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedOneConsumer.literal_singleton_coverage
#print axioms ContactedOneConsumer.literal_singleton_coverage
#check @ContactedOneConsumer.original_query_oriented
#print axioms ContactedOneConsumer.original_query_oriented
#check @ContactedOneConsumer.checked_one_caller
#print axioms ContactedOneConsumer.checked_one_caller
