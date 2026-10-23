import AdmittedFiniteSelector
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification Universal233.Rule5PaidSelector
open OrdinaryDispatch Universal233.Hard2Overlap

-- OPEN: the actual branch must produce this witness. This is a statement of
-- the next missing premise, not a theorem or an accepted caller hypothesis.
def RemainingSourceContract : Prop := ∀ (T S : Tree) (c d : Candidate),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 FastOrdinary.early T S=.hard2 c d → runHard2 T S c=some .disjoint →
 ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2 →
 selectLocal T S c.a c.b=some .remaining →
 ∃bad,selectBad T S c.a c.b=some bad ∧
  ((incident T (subtreeLabels S bad.badArc)).length=1 ∨
   (incident T (subtreeLabels S bad.badArc)).length=2)

-- OPEN independently of remaining source availability: actual selected second
-- geometry must be materialized by the literal row scan/buildOne computation.
def PaidBuilderContract : Prop := ∀ (T S : Tree) (c d : Candidate)
 (bad : BadSelection) (u v : RMAF.Vertex),
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 FastOrdinary.early T S=.hard2 c d → runHard2 T S c=some .disjoint →
 ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2 →
 selectFinal T S c.a c.b=some (.remaining bad (.second u v)) →
 ∃R,buildForSecond T S c.a c.b bad u v=some R

theorem admitted_final_available (T S : Tree) (a b : Nat)
 (guard : admitted T S a b=true)
 (remaining : selectLocal T S a b=some .remaining →
  ∃d,selectBad T S a b=some d ∧
   ((incident T (subtreeLabels S d.badArc)).length=1 ∨
    (incident T (subtreeLabels S d.badArc)).length=2)) :
 ∃z,selectFinal T S a b=some z := by
 obtain ⟨s,localPick⟩:=selectLocal_available T S a b guard
 cases s with
 | large e => exact ⟨.prefix (.large e),by rw [selectFinal,localPick]⟩
 | two c => exact ⟨.prefix (.two c),by rw [selectFinal,localPick]⟩
 | outside c => exact ⟨.prefix (.outside c),by rw [selectFinal,localPick]⟩
 | remaining =>
  obtain ⟨d,badPick,boundaryLen⟩:=remaining localPick
  obtain ⟨z,boundaryPick⟩:=(selectBoundary_available_iff T (subtreeLabels S d.badArc) d.c).mpr boundaryLen
  refine ⟨.remaining d z,?_⟩
  rw [selectFinal,localPick]
  change (selectBad T S a b).bind _=some (FinalSelection.remaining d z)
  rw [badPick]
  change (selectBoundary T (subtreeLabels S d.badArc) d.c).bind _=some (FinalSelection.remaining d z)
  rw [boundaryPick]
  rfl

theorem selected_second_built (T S : Tree) (a b : Nat)
 (d : BadSelection) (u v : RMAF.Vertex)
 (pick : selectFinal T S a b=some (.remaining d (.second u v)))
 (witness : ∃R,buildForSecond T S a b d u v=some R) :
 ∃R,buildSelected T S a b=some R := by
 obtain ⟨R,built⟩:=witness
 exact ⟨⟨d,u,v,R⟩,by simp only [buildSelected,pick,built,Option.map_some]⟩

theorem selected_second_no_refusal (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (a b q : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (pick : selectFinal T S a b=some (.remaining d (.second u v)))
 (witness : ∃R,buildForSecond T S a b d u v=some R) :
 Rule5OrdinaryDispatch.dispatch actual T S a b q≠.paidBuilderRefused := by
 obtain ⟨R,built⟩:=selected_second_built T S a b d u v pick witness
 intro refused
 have missing:=(selected_second_refusal_iff actual T S a b q d u v pick).mp refused
 rw [built] at missing
 cases missing

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.admitted_final_available
#print axioms AdmittedRule5Author.admitted_final_available
#check @AdmittedRule5Author.selected_second_built
#print axioms AdmittedRule5Author.selected_second_built
#check @AdmittedRule5Author.selected_second_no_refusal
#print axioms AdmittedRule5Author.selected_second_no_refusal
