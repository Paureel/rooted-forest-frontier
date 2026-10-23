import OriginalPaidCaseCover
import PrepareDirect
import ActualBothBadGrouped
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
set_option autoImplicit false
namespace ContactedHard2Survival

theorem original_grouped_cover (q : Nat) : OriginalGroupedCover q := by
 intro T S c d p r ord e proper selected shape picked below F agree together budget
 have parametricBelow : PaidInstances.BelowBudget OrdinaryDispatch.FastOrdinary.solve q:=below
 have covered:=actual_bothbad_grouped_cover OrdinaryDispatch.FastOrdinary.solve q T S c d p r ord e
  proper selected shape picked parametricBelow F agree together budget
 rw [original_paid_instance_binding q] at covered
 exact covered

theorem original_paid_cohabit_cover (q : Nat) (T S : Tree)
 (c d : Candidate) (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.hard2 c d) (out : Hard2Overlap.Result)
 (picked : Hard2Overlap.runHard2 T S c=some out) (nonDisjoint : out≠.disjoint)
 (below : IndependentReconstruction.BelowBudget q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2Dispatcher.paidCase (IndependentReconstruction.OwnPaid q) T S c q out).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length :=
 original_paidCase_cohabit_cover q (original_grouped_cover q) T S c d proper rejected selected out picked nonDisjoint below F agree together budget

theorem original_goodPair_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (A B C : List Nat) (q : Nat) (G : List (List Nat))
 (found : (GoodPairDP.runPair actual T S A B C q).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 unfold GoodPairDP.runPair at found
 unfold BothBad.Forest at found
 dsimp only at found
 split at found
 · cases run : AllGoodDP.run (localTarget (some T) (A++B)) (owned (OutputState.sourceForest S [A,B,C]) (A++B)) with
   | none=>rw [run] at found;cases found
   | some H=>
    rw [run] at found
    simp only [GoodPairDP.runPair.match_1] at found
    split at found
    · exact original_checked_sound found
    · cases found
 · cases found

theorem original_grouped_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (q : Nat) (G : List (List Nat))
 (found : (BothBadGrouped.executePair actual T S A B C e q).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 have valid:=(own_best_sound List.length (BothBadGrouped.accepted T S q) _ G found).1
 change (agreement T S G && decide (G.length-1≤q))=true at valid
 have facts : agreement T S G=true ∧ decide (G.length-1≤q)=true:=by simpa only [Bool.and_eq_true] using valid
 exact ⟨facts.1,of_decide_eq_true facts.2⟩

theorem original_badPair_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex) (q : Nat) (G : List (List Nat))
 (found : (Hard2Dispatcher.badPair actual T S A B C e q).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 unfold Hard2Dispatcher.badPair at found
 split at found
 · exact execute_some_sound (GenericForest.solve actual) T S q _ G found
 · exact original_grouped_sound actual T S A B C e q G found

theorem original_paidCase_sound (actual : Tree→Tree→Nat→Option (List (List Nat)))
 (T S : Tree) (c d : Candidate) (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (out : Hard2Overlap.Result) (q : Nat) (G : List (List Nat))
 (found : (Hard2Dispatcher.paidCase actual T S c q out).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q := by
 obtain ⟨p,r,shape⟩:=ContactedActualHard2.actual_two_cuts proper selected
 unfold Hard2Dispatcher.paidCase at found
 rw [shape] at found
 cases out with
 | disjoint=>exact execute_some_sound (GenericForest.solve actual) T S q _ G found
 | clique v=>exact execute_some_sound (GenericForest.solve actual) T S q _ G found
 | four ord v w=>exact execute_some_sound (GenericForest.solve actual) T S q _ G found
 | diagonal ord v w=>exact execute_some_sound (GenericForest.solve actual) T S q _ G found
 | pair ord ch=>cases ch with
  | vertex v=>exact execute_some_sound (GenericForest.solve actual) T S q _ G found
  | edge e=>
   let A:=Hard2Overlap.first ord (PaidAssembly.leftParent S p) (PaidAssembly.rightParent S r) (PaidAssembly.rootParent S p r)
   let B:=Hard2Overlap.second ord (PaidAssembly.leftParent S p) (PaidAssembly.rightParent S r) (PaidAssembly.rootParent S p r)
   let C:=Hard2Overlap.third ord (PaidAssembly.leftParent S p) (PaidAssembly.rightParent S r) (PaidAssembly.rootParent S p r)
   change (if (restrictionAgrees S T A && restrictionAgrees S T B)=true then GoodPairDP.runPair actual T S A B C q else if (restrictionAgrees S T A || restrictionAgrees S T B)=true then Hard2PaidLocal.runHardPaid actual T S q c (.pair ord (.edge e)) else Hard2Dispatcher.badPair actual T S A B C e q).answer=some G at found
   split at found
   · exact original_goodPair_sound actual T S _ _ _ q G found
   · split at found
     · exact execute_some_sound (GenericForest.solve actual) T S q _ G found
     · exact original_badPair_sound actual T S _ _ _ e q G found
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_grouped_cover
#print axioms ContactedHard2Survival.original_grouped_cover
#check @ContactedHard2Survival.original_paid_cohabit_cover
#print axioms ContactedHard2Survival.original_paid_cohabit_cover
#check @ContactedHard2Survival.original_goodPair_sound
#print axioms ContactedHard2Survival.original_goodPair_sound
#check @ContactedHard2Survival.original_grouped_sound
#print axioms ContactedHard2Survival.original_grouped_sound
#check @ContactedHard2Survival.original_badPair_sound
#print axioms ContactedHard2Survival.original_badPair_sound
#check @ContactedHard2Survival.original_paidCase_sound
#print axioms ContactedHard2Survival.original_paidCase_sound
