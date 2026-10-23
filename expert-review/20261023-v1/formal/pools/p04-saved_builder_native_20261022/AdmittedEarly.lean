import AdmittedPriority
import EarlySelector
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open OrdinaryDispatch

theorem early_hard2_guards (T S : Tree) (c d : Candidate)
 (selected : FastOrdinary.early T S=.hard2 c d) :
 select T S=some (.hard2,c) ∧ select S T=some (.hard2,d) ∧
 Rule4.select T S=none ∧ Rule4.select S T=none := by
 unfold FastOrdinary.early at selected
 split at selected <;> try cases selected
 split at selected <;> try cases selected
 split at selected <;> try cases selected
 exact ⟨by assumption,by assumption,by assumption,by assumption⟩

theorem actual_front_checks (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (selected : FastOrdinary.early T S=.hard2 c d) :
 properPair T S=true ∧ hasCherry T c.a c.b=true ∧
 earlierClear T S=true ∧ earlierClear S T=true ∧
 (cuts S c.a c.b).length=2 ∧ Rule4.select T S=none ∧ Rule4.select S T=none := by
 have guards:=early_hard2_guards T S c d selected
 have forward:=select_hard2_membership_clear T S c guards.1
 have reverse:=select_hard2_membership_clear S T d guards.2.1
 have source:=selected_candidate_source T S c forward.1
 have cutlen : (cuts S c.a c.b).length=2 := by
  have self:=(List.all_eq_true.mp forward.2) c forward.1
  change (c.originalCuts.length==2)=true at self
  have z:=beq_iff_eq.mp self
  rw [source.2] at z
  exact z
 exact ⟨proper_to_properPair T S proper,source.1,forward.2,reverse.2,cutlen,guards.2.2.1,guards.2.2.2⟩
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.early_hard2_guards
#print axioms AdmittedRule5Author.early_hard2_guards
#check @AdmittedRule5Author.actual_front_checks
#print axioms AdmittedRule5Author.actual_front_checks
