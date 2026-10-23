import OriginalCgoodCoverResume
import ActualPaidPredicateComplete
import ActualGoodPairV2
import SelectorTotalV3
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
set_option autoImplicit false
namespace ContactedHard2Survival

theorem original_goodPair_answer (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (A B C : List Nat) (q : Nat) :
 (ContactedGoodPair.runPair actual T S A B C q).answer=(GoodPairDP.runPair actual T S A B C q).answer := by
 unfold ContactedGoodPair.runPair GoodPairDP.runPair
 by_cases h : 2≤q
 · simp only [ite_eq_left h]
   cases d : AllGoodDP.run (localTarget (some T) (A++B)) (owned (OutputState.sourceForest S [A,B,C]) (A++B)) with
   | none=>rfl
   | some H=>
    simp only [ContactedGoodPair.runPair.match_1,GoodPairDP.runPair.match_1]
    by_cases m : additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H≤q-2
    · simp only [ite_eq_left m] <;> rfl
    · simp only [ite_eq_right m] <;> rfl
 · simp only [ite_eq_right h] <;> rfl

theorem original_pair_paidCase (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (c : Candidate) (p r : RMAF.Vertex) (shape : c.originalCuts=[p,r])
 (ord : ContactedHard2Overlap.Order) (e : RMAF.Vertex×RMAF.Vertex) (q : Nat) :
 let A:=ContactedHard2Overlap.first ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
 let B:=ContactedHard2Overlap.second ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
 let C:=ContactedHard2Overlap.third ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
 Hard2Dispatcher.paidCase actual T S c q (originalResult (.pair ord (.edge e)))=
 if (restrictionAgrees S T A && restrictionAgrees S T B)=true then GoodPairDP.runPair actual T S A B C q
 else if (restrictionAgrees S T A || restrictionAgrees S T B)=true then
 Hard2PaidLocal.runHardPaid actual T S q c (originalResult (.pair ord (.edge e)))
 else Hard2Dispatcher.badPair actual T S A B C e q := by
 cases ord <;> simp only [Hard2Dispatcher.paidCase,shape,originalResult,originalOrder] <;>rfl

theorem original_nonedge_paidCase (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (c : Candidate) (p r : RMAF.Vertex) (shape : c.originalCuts=[p,r])
 (out : Hard2Overlap.Result) (simple : FourPaidCases out) (q : Nat) :
 Hard2Dispatcher.paidCase actual T S c q out=Hard2PaidLocal.runHardPaid actual T S q c out := by
 cases out with
 | disjoint=>cases simple
 | clique v=>simp only [Hard2Dispatcher.paidCase,shape] <;>rfl
 | four ord v w=>simp only [Hard2Dispatcher.paidCase,shape] <;>rfl
 | diagonal ord v w=>simp only [Hard2Dispatcher.paidCase,shape] <;>rfl
 | pair ord ch=>cases ch with
   | vertex v=>simp only [Hard2Dispatcher.paidCase,shape] <;>rfl
   | edge e=>cases simple

-- Exact only missing grouped branch, kept as a consuming premise until its generic
-- prepareOne dependency is licensed or replaced. This is not whole paid coverage.
def OriginalGroupedCover (q : Nat) : Prop :=
 ∀T S c d p r ord e, DepthOne.proper T S=true→early T S=.hard2 c d→c.originalCuts=[p,r]→
 Hard2Overlap.runHard2 T S c=some (originalResult (.pair ord (.edge e)))→
 IndependentReconstruction.BelowBudget q→
 ∀F,agreement T S F=true→(∃D,D∈F ∧ c.a∈D ∧ c.b∈D)→F.length-1≤q→
 ∃G,(BothBadGrouped.executePair (IndependentReconstruction.OwnPaid q) T S
  (ContactedHard2Overlap.first ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))
  (ContactedHard2Overlap.second ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r))
  (ContactedHard2Overlap.third ord (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)) e q).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length

theorem original_paidCase_cohabit_cover (q : Nat) (grouped : OriginalGroupedCover q) (T S : Tree)
 (c d : Candidate) (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.hard2 c d) (out : Hard2Overlap.Result)
 (picked : Hard2Overlap.runHard2 T S c=some out) (nonDisjoint : out≠.disjoint)
 (below : IndependentReconstruction.BelowBudget q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2Dispatcher.paidCase (IndependentReconstruction.OwnPaid q) T S c q out).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨p,r,shape⟩:=ContactedActualHard2.actual_two_cuts proper selected
 have parametricBelow : PaidInstances.BelowBudget OrdinaryDispatch.FastOrdinary.solve q:=below
 by_cases simple : FourPaidCases out
 · have covered:=original_four_paid_cases_cover OrdinaryDispatch.FastOrdinary.solve q T S c d proper selected out picked simple parametricBelow F agree together budget
   rw [original_paid_instance_binding q] at covered
   rw [original_nonedge_paidCase _ T S c p r shape out simple q]
   exact covered
 · cases out with
   | disjoint=>exact False.elim (nonDisjoint rfl)
   | clique v=>exact False.elim (simple True.intro)
   | four ord v w=>exact False.elim (simple True.intro)
   | diagonal ord v w=>exact False.elim (simple True.intro)
   | pair ord ch=>cases ch with
    | vertex v=>exact False.elim (simple True.intro)
    | edge e=>
     let o:=contactedOrder ord
     have ori : originalOrder o=ord:=by cases ord <;>rfl
     have picked' : Hard2Overlap.runHard2 T S c=some (originalResult (.pair o (.edge e))):=by change Hard2Overlap.runHard2 T S c=some (.pair (originalOrder o) (.edge e));rw [ori];exact picked
     have ownPicked:=original_selector_picked T S c (.pair o (.edge e)) picked'
     let A:=ContactedHard2Overlap.first o (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
     let B:=ContactedHard2Overlap.second o (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
     let C:=ContactedHard2Overlap.third o (ContactedHard2Parent.leftParent S p) (ContactedHard2Parent.rightParent S r) (ContactedHard2Parent.rootParent S p r)
     have route:=original_pair_paidCase (IndependentReconstruction.OwnPaid q) T S c p r shape o e q
     change Hard2Dispatcher.paidCase _ T S c q (originalResult (.pair o (.edge e)))=_ at route
     rw [show Hard2Overlap.Result.pair ord (.edge e)=originalResult (.pair o (.edge e)) from by change Hard2Overlap.Result.pair ord (.edge e)=.pair (originalOrder o) (.edge e);rw [ori],route]
     change ∃G,(if (restrictionAgrees S T A && restrictionAgrees S T B)=true then GoodPairDP.runPair (IndependentReconstruction.OwnPaid q) T S A B C q else if (restrictionAgrees S T A || restrictionAgrees S T B)=true then Hard2PaidLocal.runHardPaid (IndependentReconstruction.OwnPaid q) T S q c (originalResult (.pair o (.edge e))) else Hard2Dispatcher.badPair (IndependentReconstruction.OwnPaid q) T S A B C e q).answer=some G ∧ agreement T S G=true ∧ G.length≤F.length
     by_cases ga : restrictionAgrees S T A=true
     · by_cases gb : restrictionAgrees S T B=true
       · have covered:=ContactedActualHard2.selected_pair_cover OrdinaryDispatch.FastOrdinary.solve q T S c d p r proper rejected selected shape o (.edge e) ownPicked ga gb parametricBelow F agree together budget
         rw [original_paid_instance_binding q] at covered
         obtain ⟨G,runG,ag,least⟩:=covered
         have rg : (GoodPairDP.runPair (IndependentReconstruction.OwnPaid q) T S A B C q).answer=some G:=by
          rw [←original_goodPair_answer]
          exact runG
         exact ⟨G,by rw [show (restrictionAgrees S T A && restrictionAgrees S T B)=true from by simp only [ga,gb,Bool.and_self],ite_eq_left rfl];exact rg,ag,least⟩
       · have covered:=original_actualPaidCase_complete OrdinaryDispatch.FastOrdinary.solve q T S c d proper selected _ picked'
          (by unfold Hard2PaidLocal.actualPaidCase;rw [shape];change restrictionAgrees S T (Hard2Overlap.first (originalOrder o) _ _ _)=true ∨ restrictionAgrees S T (Hard2Overlap.second (originalOrder o) _ _ _)=true;rw [first_original,second_original];exact Or.inl ga) parametricBelow F agree together budget
         rw [original_paid_instance_binding q] at covered
         simpa only [ga,show restrictionAgrees S T B=false from Bool.eq_false_iff.mpr gb,Bool.true_and,Bool.false_eq_true,Bool.true_or,ite_false,ite_true] using covered
     · have ba : restrictionAgrees S T A=false:=Bool.eq_false_iff.mpr ga
       by_cases gb : restrictionAgrees S T B=true
       · have covered:=original_actualPaidCase_complete OrdinaryDispatch.FastOrdinary.solve q T S c d proper selected _ picked'
          (by unfold Hard2PaidLocal.actualPaidCase;rw [shape];change restrictionAgrees S T (Hard2Overlap.first (originalOrder o) _ _ _)=true ∨ restrictionAgrees S T (Hard2Overlap.second (originalOrder o) _ _ _)=true;rw [first_original,second_original];exact Or.inr gb) parametricBelow F agree together budget
         rw [original_paid_instance_binding q] at covered
         simpa only [ba,gb,Bool.false_and,Bool.false_eq_true,Bool.false_or,ite_false,ite_true] using covered
       · have bb : restrictionAgrees S T B=false:=Bool.eq_false_iff.mpr gb
         simp only [ba,bb,Bool.false_and,Bool.false_or,Bool.false_eq_true,ite_false]
         by_cases gc : restrictionAgrees S T C=true
         · have covered:=original_actual_bothbad_cgood_cover q T S c d p r o e proper selected shape picked' below ba bb gc F agree together budget
           simpa only [Hard2Dispatcher.badPair,gc,ite_true,BothBadLocal.runPair] using covered
         · have covered:=grouped T S c d p r o e proper selected shape picked' below F agree together budget
           obtain ⟨G,rg,ag,least⟩:=covered
           refine ⟨G,?_,ag,least⟩
           change (Hard2Dispatcher.badPair (IndependentReconstruction.OwnPaid q) T S A B C e q).answer=some G
           unfold Hard2Dispatcher.badPair
           rw [ite_eq_right gc]
           exact rg
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_goodPair_answer
#print axioms ContactedHard2Survival.original_goodPair_answer
#check @ContactedHard2Survival.original_pair_paidCase
#print axioms ContactedHard2Survival.original_pair_paidCase
#check @ContactedHard2Survival.original_nonedge_paidCase
#print axioms ContactedHard2Survival.original_nonedge_paidCase
#check @ContactedHard2Survival.original_paidCase_cohabit_cover
#print axioms ContactedHard2Survival.original_paidCase_cohabit_cover
