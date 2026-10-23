import ActualPaidDiagonal
open RMAF VertexGeometry Universal233 Universal233.CherryBranching
open ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

def contactedOrder : Hard2Overlap.Order→Order
 | .abc=>.abc | .acb=>.acb | .bac=>.bac | .bca=>.bca

def contactedResult : Hard2Overlap.Result→Result
 | .disjoint=>.disjoint
 | .clique v=>.clique v
 | .four o v w=>.four (contactedOrder o) v w
 | .diagonal o v w=>.diagonal (contactedOrder o) v w
 | .pair o c=>.pair (contactedOrder o) c

theorem original_contacted_inverse (out : Result) : contactedResult (originalResult out)=out := by
 cases out with
 | disjoint=>rfl
 | clique v=>rfl
 | four o v w=>cases o <;>rfl
 | diagonal o v w=>cases o <;>rfl
 | pair o c=>cases o <;>rfl

theorem contacted_original_inverse (out : Hard2Overlap.Result) : originalResult (contactedResult out)=out := by
 cases out with
 | disjoint=>rfl
 | clique v=>rfl
 | four o v w=>cases o <;>rfl
 | diagonal o v w=>cases o <;>rfl
 | pair o c=>cases o <;>rfl

theorem original_selector_picked (T S : Tree) (c : Candidate) (out : Result)
 (picked : Hard2Overlap.runHard2 T S c=some (originalResult out)) :
 ContactedActualHard2.runHard2 T S c=some out := by
 rw [actual_runHard2_original] at picked
 cases h : ContactedActualHard2.runHard2 T S c with
 | none=>simp only [h,Option.map_none] at picked;cases picked
 | some z=>
  have eq : originalResult z=originalResult out := Option.some.inj (by simpa only [h,Option.map_some] using picked)
  have zeq:=congrArg contactedResult eq
  rw [original_contacted_inverse,original_contacted_inverse] at zeq
  exact congrArg some zeq
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_contacted_inverse
#print axioms ContactedHard2Survival.original_contacted_inverse
#check @ContactedHard2Survival.contacted_original_inverse
#print axioms ContactedHard2Survival.contacted_original_inverse
#check @ContactedHard2Survival.original_selector_picked
#print axioms ContactedHard2Survival.original_selector_picked
