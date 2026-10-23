import AdmittedSelectedBadPattern
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap

-- The exact literal selected value is transported; this theorem does not
-- assume or claim that the actual remaining branch already has such a value.
theorem actual_selected_bad_partition_check (T S : Tree) (c d : Candidate) (bad : BadSelection)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (pick : selectBad T S c.a c.b=some bad) :
 partitionCheck (leaves T) [subtreeLabels S bad.badArc,[bad.c],coreLabels S c.a c.b]=true := by
 have facts:(decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧
  decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 have hnS:(leaves S).Nodup:=of_decide_eq_true facts.1.2
 have labels:(leaves T).Perm (leaves S):=of_decide_eq_true facts.2
 have endpoints:=actual_source_endpoint_members T S c d proper early
 have sourceCheck:=pendant_partition_check (a:=c.a) (b:=c.b) hnS endpoints.1
 have targetCheck:=partition_check_labels_perm (leaves S) (leaves T)
  (pendantPartition S c.a c.b) labels.symm sourceCheck
 have len:=(actual_front_checks T S c d proper early).2.2.2.2.1
 exact partition_check_blocks_perm (leaves T) _ _
  (selected_bad_partition_perm T S c.a c.b bad len pick) targetCheck

theorem actual_selected_bad_incident_length (T S : Tree) (c d : Candidate) (bad : BadSelection)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (pick : selectBad T S c.a c.b=some bad) :
 ((incident T (subtreeLabels S bad.badArc)).length=1 ∨
  (incident T (subtreeLabels S bad.badArc)).length=2) := by
 have facts:(decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧
  decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 have hnT:(leaves T).Nodup:=of_decide_eq_true facts.1.1
 have len:=(actual_front_checks T S c d proper early).2.2.2.2.1
 have embedding:=selected_bad_target_embeddings T S c.a c.b bad len pick
  (actual_target_embeddings T S c d proper early graph)
 have partition:=actual_selected_bad_partition_check T S c d bad proper early pick
 rcases incident_one_or_two hnT partition embedding with ⟨q,one⟩|⟨q,r,two⟩
 · exact Or.inl (by rw [one];rfl)
 · exact Or.inr (by rw [two];rfl)

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.actual_selected_bad_partition_check
#print axioms AdmittedRule5Author.actual_selected_bad_partition_check
#check @AdmittedRule5Author.actual_selected_bad_incident_length
#print axioms AdmittedRule5Author.actual_selected_bad_incident_length
