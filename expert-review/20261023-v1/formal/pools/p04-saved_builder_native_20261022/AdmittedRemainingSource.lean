import AdmittedSelectedBadIncident
import AdmittedRemainingObstruction
import AdmittedTerminalWitness
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap

theorem literal_boundary_mem_cuts (S : Tree) (a b : Nat) (v : Vertex)
 (member:v∈Universal233.HardParent.vertices S) (nonempty:v≠[])
 (parent:v.dropLast∈minimalVertices [a,b] S) (outside:v∉minimalVertices [a,b] S) :
 v∈cuts S a b := by
 have parentHit:(minimalVertices [a,b] S).contains v.dropLast=true:=List.contains_iff_mem.mpr parent
 have outsideHit:(minimalVertices [a,b] S).contains v=false := by
  cases hit:(minimalVertices [a,b] S).contains v with
  | false => rfl
  | true => exact False.elim (outside (List.contains_iff_mem.mp hit))
 have notnil:v.isEmpty=false := by
  cases v with | nil => contradiction | cons x xs => rfl
 change v∈(Universal233.HardParent.vertices S).filter _
 exact List.mem_filter.mpr ⟨member,by simp only [notnil,parentHit,outsideHit,Bool.not_false,Bool.true_and]⟩

theorem actual_cut_leaf_boundary (S : Tree) (a b : Nat)
 (allLeaf:∀v∈cuts S a b,∃x,subtree S v=some (.leaf x)) :
 LeafBoundary S (minimalVertices [a,b] S) := by
 intro v member nonempty parent outside
 exact allLeaf v (literal_boundary_mem_cuts S a b v member nonempty parent outside)

theorem two_distinct_members_length {α : Type} (L : List α) (a b : α)
 (ha:a∈L) (hb:b∈L) (neq:a≠b) : 2≤L.length := by
 cases L with
 | nil => cases ha
 | cons x tail =>
  cases tail with
  | nil => exact False.elim (neq ((List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm))
  | cons y rest => simp only [List.length_cons];omega

theorem endpoint_pair_selected_count (S : Tree) (a b : Nat)
 (ha:a∈leaves S) (hb:b∈leaves S) (neq:a≠b) :
 2≤((leaves S).filter ([a,b].contains)).length := by
 apply two_distinct_members_length _ a b
 · exact List.mem_filter.mpr ⟨ha,by simp⟩
 · exact List.mem_filter.mpr ⟨hb,by simp⟩
 · exact neq

theorem actual_all_leaf_cuts_contradiction (T S : Tree) (c d : Candidate)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (allLeaf:∀v∈cuts S c.a c.b,∃x,subtree S v=some (.leaf x)) : False := by
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have hnT:(leaves T).Nodup:=priority.1
 have hnS:(leaves S).Nodup:=priority.2.1
 have original:=hasCherry_bool_prop T c.a c.b front.2.1
 have neq:=hasCherry_ne original hnT
 have endpoints:=actual_source_endpoint_members T S c d proper early
 have count:=endpoint_pair_selected_count S c.a c.b endpoints.1 endpoints.2 neq
 have terminal:=minimal_two_terminal [c.a,c.b] S count (actual_cut_leaf_boundary S c.a c.b allLeaf)
 obtain ⟨x,y,cherry,hit,partner⟩:=terminal
 have xchoices:x=c.a ∨ x=c.b := by
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.contains_iff_mem.mp hit)
 have noCommon:¬HasCherry c.a c.b S := by
  intro common
  have zero:=commonCherry_zeroCuts S c.a c.b hnS common
  have len:=front.2.2.2.2.1
  change (pendantOriginal S c.a c.b).length=2 at len
  rw [zero] at len
  cases len
 rcases partner with good|exit
 · have ychoices:y=c.a ∨ y=c.b := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.contains_iff_mem.mp good)
   rcases xchoices with rfl|rfl <;> rcases ychoices with rfl|rfl
   · exact hasCherry_ne cherry hnS rfl
   · exact noCommon cherry
   · exact noCommon (hasCherry_prop_swap cherry)
   · exact hasCherry_ne cherry hnS rfl
 · obtain ⟨q,member,nonempty,parent,outside,leaf⟩:=exit
   have cut:=literal_boundary_mem_cuts S c.a c.b q member nonempty parent outside
   obtain ⟨r,order⟩:=two_list_perm_member (cuts S c.a c.b) q front.2.2.2.2.1 cut
   have single:=source_labels_of_subtree S q (.leaf y) leaf
   rcases xchoices with rfl|rfl
   · have guard:Rule4.LocalGuard T S ⟨c.a,c.b,y,q,r⟩ :=
      ⟨Rule4.orderedCherries_complete original,Rule4.orderedCherries_complete cherry,neq,order,single⟩
     obtain ⟨choice,picked⟩:=Rule4.select_complete priority _ guard
     rw [front.2.2.2.2.2.1] at picked
     cases picked
   · have reverseOrder:(pendantOriginal S c.b c.a).Perm [q,r] := by
      rw [pendantOriginal_swap S c.b c.a]
      exact order
     have guard:Rule4.LocalGuard T S ⟨c.b,c.a,y,q,r⟩ :=
      ⟨Rule4.orderedCherries_complete (hasCherry_prop_swap original),Rule4.orderedCherries_complete cherry,
       Ne.symm neq,reverseOrder,single⟩
     obtain ⟨choice,picked⟩:=Rule4.select_complete priority _ guard
     rw [front.2.2.2.2.2.1] at picked
     cases picked

theorem actual_remaining_bad_available (T S : Tree) (c d : Candidate)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (two:((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2)
 (remaining:selectLocal T S c.a c.b=some .remaining) :
 ∃bad,selectBad T S c.a c.b=some bad := by
 cases pick:selectBad T S c.a c.b with
 | some bad => exact ⟨bad,rfl⟩
 | none =>
  exact False.elim (actual_all_leaf_cuts_contradiction T S c d proper early
   (remaining_no_bad_every_cut_leaf T S c.a c.b remaining two pick))

theorem remaining_source_contract : RemainingSourceContract := by
 intro T S c d proper _pretest early graph two remaining
 obtain ⟨bad,pick⟩:=actual_remaining_bad_available T S c d proper early two remaining
 exact ⟨bad,pick,actual_selected_bad_incident_length T S c d bad proper early graph pick⟩

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.literal_boundary_mem_cuts
#print axioms AdmittedRule5Author.literal_boundary_mem_cuts
#check @AdmittedRule5Author.actual_cut_leaf_boundary
#print axioms AdmittedRule5Author.actual_cut_leaf_boundary
#check @AdmittedRule5Author.two_distinct_members_length
#print axioms AdmittedRule5Author.two_distinct_members_length
#check @AdmittedRule5Author.endpoint_pair_selected_count
#print axioms AdmittedRule5Author.endpoint_pair_selected_count
#check @AdmittedRule5Author.actual_all_leaf_cuts_contradiction
#print axioms AdmittedRule5Author.actual_all_leaf_cuts_contradiction
#check @AdmittedRule5Author.actual_remaining_bad_available
#print axioms AdmittedRule5Author.actual_remaining_bad_available
#check @AdmittedRule5Author.remaining_source_contract
#print axioms AdmittedRule5Author.remaining_source_contract
