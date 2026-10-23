import AdmittedPartitionTransport
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch

theorem two_members_perm (L : List Vertex) (e f : Vertex) (len : L.length=2)
 (he : e∈L) (hf : f∈L) (neq : e≠f) : L.Perm [e,f] := by
 obtain ⟨r,order⟩:=two_list_perm_member L e len he
 have member : f∈[e,r]:=order.mem_iff.mp hf
 have choices : f=e ∨ f=r:=by simpa only [List.mem_cons,List.not_mem_nil,or_false] using member
 rcases choices with same|same
 · exact False.elim (neq same.symm)
 · subst r
   exact order

theorem selected_bad_partition_perm (T S : Tree) (a b : Nat) (d : BadSelection)
 (len : (cuts S a b).length=2) (pick : selectBad T S a b=some d) :
 (pendantPartition S a b).Perm [subtreeLabels S d.badArc,[d.c],coreLabels S a b] := by
 have facts:=selectBad_sound T S a b d pick
 have order:=two_members_perm (cuts S a b) d.badArc d.singletonArc len facts.1 facts.2.1 facts.2.2.1
 have single:=source_labels_of_subtree S d.singletonArc (.leaf d.c) facts.2.2.2.2
 have parts:=(order.map (subtreeLabels S)).append_right [coreLabels S a b]
 change ((cuts S a b).map (subtreeLabels S)++[coreLabels S a b]).Perm
  [subtreeLabels S d.badArc,subtreeLabels S d.singletonArc,coreLabels S a b] at parts
 rw [single] at parts
 exact parts

theorem selected_bad_target_embeddings (T S : Tree) (a b : Nat) (d : BadSelection)
 (len : (cuts S a b).length=2) (pick : selectBad T S a b=some d)
 (embedding : pairwiseEmbeddings T (pendantPartition S a b)=true) :
 pairwiseEmbeddings T [subtreeLabels S d.badArc,[d.c],coreLabels S a b]=true :=
 pairwise_embeddings_perm T _ _ (selected_bad_partition_perm T S a b d len pick) embedding

theorem cherry_original_members {T : Tree} {a b : Nat} (cherry : HasCherry a b T) :
 a∈leaves T ∧ b∈leaves T := by
 induction cherry with
 | here => exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ List.mem_cons_self⟩
 | swap => exact ⟨List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩
 | left h ih => exact ⟨List.mem_append_left _ ih.1,List.mem_append_left _ ih.2⟩
 | right h ih => exact ⟨List.mem_append_right _ ih.1,List.mem_append_right _ ih.2⟩

theorem actual_source_endpoint_members (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (early : FastOrdinary.early T S=.hard2 c d) :
 c.a∈leaves S ∧ c.b∈leaves S := by
 have priority:=actual_rule4_priority_closed T S c d proper early
 have front:=actual_front_checks T S c d proper early
 have members:=cherry_original_members (hasCherry_bool_prop T c.a c.b front.2.1)
 exact ⟨priority.2.2.1.mem_iff.mp members.1,priority.2.2.1.mem_iff.mp members.2⟩

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.two_members_perm
#print axioms AdmittedRule5Author.two_members_perm
#check @AdmittedRule5Author.selected_bad_partition_perm
#print axioms AdmittedRule5Author.selected_bad_partition_perm
#check @AdmittedRule5Author.selected_bad_target_embeddings
#print axioms AdmittedRule5Author.selected_bad_target_embeddings
#check @AdmittedRule5Author.cherry_original_members
#print axioms AdmittedRule5Author.cherry_original_members
#check @AdmittedRule5Author.actual_source_endpoint_members
#print axioms AdmittedRule5Author.actual_source_endpoint_members
