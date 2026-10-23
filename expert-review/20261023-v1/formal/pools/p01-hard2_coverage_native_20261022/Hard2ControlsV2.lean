import ForwardCallbacksComplete
open RMAF Universal233 Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedHard2

def controlTree : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def controlAF : List (List Nat) := [[0],[1],[2]]
def forged : Candidate := {parent:=[],a:=0,b:=1,originalCuts:=[[false],[true]]}
theorem separated_endpoints_control : DepthOne.proper controlTree controlTree=true ∧
 agreement controlTree controlTree controlAF=true ∧
 ¬∃B∈controlAF,0∈B ∧ 1∈B := by
 refine ⟨by decide,by decide,?_⟩
 simp [controlAF]
theorem forged_count_not_selection_control : forged.originalCuts.length=2 ∧
 early controlTree controlTree≠.hard2 forged forged := by
 refine ⟨rfl,?_⟩
 intro h
 have answer : early controlTree controlTree=.common false {parent:=[false],a:=0,b:=1,originalCuts:=[]} := rfl
 rw [answer] at h
 cases h
end ContactedHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2.separated_endpoints_control
#print axioms ContactedHard2.separated_endpoints_control
#check @ContactedHard2.forged_count_not_selection_control
#print axioms ContactedHard2.forged_count_not_selection_control
