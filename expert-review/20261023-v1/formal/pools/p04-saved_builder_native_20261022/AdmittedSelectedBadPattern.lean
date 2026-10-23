import AdmittedRemainingPartition
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap

-- Exact facts about the bad value returned by the literal scan, with no
-- source-pattern or desired availability witness supplied as a hypothesis.
theorem selected_bad_two_good_pattern (T S : Tree) (a b : Nat) (d : BadSelection)
 (len : (cuts S a b).length=2) (pick : selectBad T S a b=some d)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2) :
 restrictionAgrees T S [d.c]=true ∧
 restrictionAgrees T S (coreLabels S a b)=true := by
 have facts:=selectBad_sound T S a b d pick
 have bad:=facts.2.2.2.1
 have order:=selected_bad_partition_perm T S a b d len pick
 have reordered:(([subtreeLabels S d.badArc,[d.c],coreLabels S a b]).filter
  (restrictionAgrees T S)).length=2 := by
   rw [←(order.filter (restrictionAgrees T S)).length_eq]
   exact two
 cases single:restrictionAgrees T S [d.c] <;>
  cases core:restrictionAgrees T S (coreLabels S a b) <;>
  simp only [List.filter_cons,List.filter_nil,bad,single,core,
   Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_nil] at reordered
 all_goals first | exact ⟨rfl,rfl⟩ | omega

theorem selected_bad_labels_nonempty (T S : Tree) (a b : Nat) (d : BadSelection)
 (pick : selectBad T S a b=some d) : (subtreeLabels S d.badArc)≠[] := by
 have facts:=selectBad_sound T S a b d pick
 obtain ⟨U,location⟩:=actual_cut_valid S a b d.badArc facts.1
 have labels:=source_labels_of_subtree S d.badArc U location
 have positive:=tree_leaf_count_positive U
 intro empty
 rw [←labels,empty] at positive
 cases positive

theorem actual_selected_bad_pattern (T S : Tree) (c d : Candidate) (bad : BadSelection)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2)
 (pick : selectBad T S c.a c.b=some bad) :
 (pendantPartition S c.a c.b).Perm
  [subtreeLabels S bad.badArc,[bad.c],coreLabels S c.a c.b] ∧
 pairwiseEmbeddings T [subtreeLabels S bad.badArc,[bad.c],coreLabels S c.a c.b]=true ∧
 restrictionAgrees T S [bad.c]=true ∧
 restrictionAgrees T S (coreLabels S c.a c.b)=true ∧
 (subtreeLabels S bad.badArc)≠[] := by
 have len:=(actual_front_checks T S c d proper early).2.2.2.2.1
 have pattern:=selected_bad_two_good_pattern T S c.a c.b bad len pick two
 exact ⟨selected_bad_partition_perm T S c.a c.b bad len pick,
  selected_bad_target_embeddings T S c.a c.b bad len pick
   (actual_target_embeddings T S c d proper early graph),
  pattern.1,pattern.2,selected_bad_labels_nonempty T S c.a c.b bad pick⟩

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.selected_bad_two_good_pattern
#print axioms AdmittedRule5Author.selected_bad_two_good_pattern
#check @AdmittedRule5Author.selected_bad_labels_nonempty
#print axioms AdmittedRule5Author.selected_bad_labels_nonempty
#check @AdmittedRule5Author.actual_selected_bad_pattern
#print axioms AdmittedRule5Author.actual_selected_bad_pattern
