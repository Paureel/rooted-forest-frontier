import UnitWitness03
import ControlFlowV4
namespace UnitPaidCombination
open RMAF Universal233 Universal233.CherryBranching Universal233.BothBad OrdinaryDispatch

theorem own_paid_below (q : Nat) (below : IndependentReconstruction.BelowBudget q) :
    Below q (IndependentReconstruction.OwnPaid q) := by
 intro r strict T S proper
 simpa only [IndependentReconstruction.OwnPaid,dif_pos strict] using below r strict T S proper

theorem original_combine_query_exact (T S : Tree) (c : Candidate) (q : Nat)
    (paid : Execution) (proper : DepthOne.proper T S=true)
    (selected : Universal233.CherryBranching.select T S=some (.hard2,c))
    (below : IndependentReconstruction.BelowBudget q)
    (paidCover : CohabitingPaidCover T S c q paid) :
    QueryExact T S q
      (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q paid).answer :=
 combine_query_exact _ T S c q paid proper selected (own_paid_below q below) paidCover

theorem original_combine_some (T S : Tree) (c : Candidate) (q : Nat)
    (paid : Execution) (proper : DepthOne.proper T S=true)
    (selected : Universal233.CherryBranching.select T S=some (.hard2,c))
    (below : IndependentReconstruction.BelowBudget q)
    (paidCover : CohabitingPaidCover T S c q paid)
    (G : OrdinaryDispatch.Forest)
    (result : (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q paid).answer=some G) :
    agreement T S G=true ∧ G.length-1≤q ∧
      ∀ F,agreement T S F=true → G.length≤F.length := by
 have exactness:=original_combine_query_exact T S c q paid proper selected below paidCover
 simpa only [result,QueryExact] using exactness

theorem original_combine_none_iff (T S : Tree) (c : Candidate) (q : Nat)
    (paid : Execution) (proper : DepthOne.proper T S=true)
    (selected : Universal233.CherryBranching.select T S=some (.hard2,c))
    (below : IndependentReconstruction.BelowBudget q)
    (paidCover : CohabitingPaidCover T S c q paid) :
    (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q paid).answer=none ↔
      ∀ F,agreement T S F=true → q<F.length-1 := by
 have exactness:=original_combine_query_exact T S c q paid proper selected below paidCover
 cases result : (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q paid).answer with
 | none => simpa only [result,QueryExact,true_iff] using exactness
 | some G =>
   have facts : agreement T S G=true ∧ G.length-1≤q ∧
       ∀ F,agreement T S F=true → G.length≤F.length := by
     simpa only [result,QueryExact] using exactness
   simp only [Option.some_ne_none,false_iff]
   intro impossible
   have bad:=impossible G facts.1
   omega

theorem checked_paid_cover (T S : Tree) (c : Candidate) (q : Nat)
    (paid : Execution) (raw : Option OrdinaryDispatch.Forest)
    (checkedAnswer : paid.answer=checked T S q raw)
    (cover : ∀ F,agreement T S F=true → F.length-1≤q → Cohabit c.a c.b F →
      ∃ G,paid.answer=some G ∧ G.length≤F.length) : CohabitingPaidCover T S c q paid := by
 refine ⟨?_,cover⟩
 intro G found
 exact checked_sound T S q raw G (checkedAnswer.symm.trans found)

theorem literal_unit_paid_tie (actual : Hard2Combine.Ordinary) (T S : Tree)
    (a b q : Nat) (paid : Execution) (U P : OrdinaryDispatch.Forest)
    (units : runChildren actual T S q [singletonChild S a,singletonChild S b]=some U)
    (paidResult : paid.answer=some P) (tie : U.length=P.length) :
    (Hard2Combine.combine actual T S a b q paid).answer=some U := by
 simp only [Hard2Combine.combine,units,paidResult]
 exact choose_first_tie U P tie
end UnitPaidCombination

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @UnitPaidCombination.own_paid_below
#print axioms UnitPaidCombination.own_paid_below
#check @UnitPaidCombination.original_combine_query_exact
#print axioms UnitPaidCombination.original_combine_query_exact
#check @UnitPaidCombination.original_combine_some
#print axioms UnitPaidCombination.original_combine_some
#check @UnitPaidCombination.original_combine_none_iff
#print axioms UnitPaidCombination.original_combine_none_iff
#check @UnitPaidCombination.checked_paid_cover
#print axioms UnitPaidCombination.checked_paid_cover
#check @UnitPaidCombination.literal_unit_paid_tie
#print axioms UnitPaidCombination.literal_unit_paid_tie
