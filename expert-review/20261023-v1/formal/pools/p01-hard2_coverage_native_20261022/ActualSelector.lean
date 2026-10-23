import SelectorValidity
import PairInterface
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedActualHard2

theorem actual_selector_some_valid {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) :
 ∃p r out,c.originalCuts=[p,r] ∧ runHard2 T S c=some out ∧
 Valid T (leftParent S p) (rightParent S r) (rootParent S p r) out := by
 obtain ⟨p,r,shape⟩:=actual_two_cuts proper selected
 have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ (List.Perm.refl _)
 obtain ⟨out,found⟩:=select_total T S _ _ _ proper checks.1
 have valid:=select_valid T S _ _ _ proper checks.1 out found
 exact ⟨p,r,out,shape,by simpa only [runHard2,shape] using found,valid⟩
end ContactedActualHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedActualHard2.actual_selector_some_valid
#print axioms ContactedActualHard2.actual_selector_some_valid
