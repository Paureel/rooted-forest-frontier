import PaidTerminalFork
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap AdmittedRule5Author

theorem subtree_append_local (S : Tree) (p : Vertex) (U : Tree) (q : Vertex)
 (location:subtree S p=some U) : subtree S (p++q)=subtree U q := by
 induction p generalizing S with
 | nil => cases Option.some.inj location;rfl
 | cons side rest ih =>
  cases S with
  | leaf x => cases location
  | node l r => cases side <;> exact ih _ location

theorem endpointForkTree_child (S : Tree) (p : Vertex) (side : Bool) (a : Nat) (U : Tree)
 (location:subtree S p=some (endpointForkTree side a U)) :
 subtree S (p++[!side])=some U := by
 rw [subtree_append_local S p _ [!side] location]
 cases side <;> rfl

theorem subtree_cherry_local (S : Tree) (p : Vertex) (a b : Nat)
 (location:subtree S p=some (.node (.leaf a) (.leaf b))) : HasCherry a b S := by
 induction p generalizing S with
 | nil => cases Option.some.inj location;exact .here
 | cons side rest ih =>
  cases S with
  | leaf x => cases location
  | node l r =>
   cases side with
   | false => exact .left (ih l location)
   | true => exact .right (ih r location)

theorem endpointForkTree_cherry (S : Tree) (p : Vertex) (side : Bool) (a b : Nat)
 (location:subtree S p=some (endpointForkTree side a (.leaf b))) : HasCherry a b S := by
 cases side with
 | false => exact subtree_cherry_local S p a b location
 | true => exact hasCherry_prop_swap (subtree_cherry_local S p b a location)

theorem actual_terminal_impossible (T S : Tree) (c d : Candidate)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (terminal:EndpointTerminal [c.a,c.b] S (minimalVertices [c.a,c.b] S)) : False := by
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have hnT:(leaves T).Nodup:=priority.1
 have hnS:(leaves S).Nodup:=priority.2.1
 have original:=hasCherry_bool_prop T c.a c.b front.2.1
 have neq:=hasCherry_ne original hnT
 obtain ⟨x,y,cherry,hit,partner⟩:=terminal
 have xchoices:x=c.a ∨ x=c.b := by
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.contains_iff_mem.mp hit)
 have noCommon:¬HasCherry c.a c.b S := by
  intro common
  have zero:=commonCherry_zeroCuts S c.a c.b hnS common
  have len:=front.2.2.2.2.1
  change (pendantOriginal S c.a c.b).length=2 at len
  rw [zero] at len;cases len
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
     rw [front.2.2.2.2.2.1] at picked;cases picked
   · have reverseOrder:(pendantOriginal S c.b c.a).Perm [q,r] := by
      rw [pendantOriginal_swap S c.b c.a];exact order
     have guard:Rule4.LocalGuard T S ⟨c.b,c.a,y,q,r⟩ :=
      ⟨Rule4.orderedCherries_complete (hasCherry_prop_swap original),Rule4.orderedCherries_complete cherry,
       Ne.symm neq,reverseOrder,single⟩
     obtain ⟨choice,picked⟩:=Rule4.select_complete priority _ guard
     rw [front.2.2.2.2.2.1] at picked;cases picked

theorem selected_bad_cut_cases (T S : Tree) (a b : Nat) (bad : BadSelection)
 (len:(cuts S a b).length=2) (pick:selectBad T S a b=some bad) :
 ∀v∈cuts S a b,v=bad.badArc ∨ v=bad.singletonArc := by
 have facts:=selectBad_sound T S a b bad pick
 have order:=two_members_perm (cuts S a b) bad.badArc bad.singletonArc len facts.1 facts.2.1 facts.2.2.1
 intro v member
 simpa only [List.mem_cons,List.not_mem_nil,or_false] using (order.mem_iff.mp member)

theorem actual_selected_bad_endpoint_fork (T S : Tree) (c d : Candidate) (bad : BadSelection)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (pick:selectBad T S c.a c.b=some bad) :
 ∃U p side a b,(a=c.a ∧ b=c.b ∨ a=c.b ∧ b=c.a) ∧
  subtree S bad.badArc=some U ∧ bad.badArc=p++[!side] ∧
  subtree S p=some (endpointForkTree side a U) := by
 have front:=actual_front_checks T S c d proper early
 have priority:=actual_rule4_priority_closed T S c d proper early
 have original:=hasCherry_bool_prop T c.a c.b front.2.1
 have neq:=hasCherry_ne original priority.1
 have endpoints:=actual_source_endpoint_members T S c d proper early
 have count:=endpoint_pair_selected_count S c.a c.b endpoints.1 endpoints.2 neq
 have facts:=selectBad_sound T S c.a c.b bad pick
 obtain ⟨U,badLocation⟩:=actual_cut_valid S c.a c.b bad.badArc facts.1
 have casesCut:=selected_bad_cut_cases T S c.a c.b bad front.2.2.2.2.1 pick
 have boundary:LeafOrTreeBoundary S (minimalVertices [c.a,c.b] S) U := by
  intro v exit
  have cut:=literal_boundary_mem_cuts S c.a c.b v exit.1 exit.2.1 exit.2.2.1 exit.2.2.2
  rcases casesCut v cut with rfl|rfl
  · exact Or.inr badLocation
  · exact Or.inl ⟨bad.c,facts.2.2.2.2⟩
 rcases minimal_two_terminal_or_fork [c.a,c.b] S U count boundary with terminal|fork
 · exact False.elim (actual_terminal_impossible T S c d proper early terminal)
 · obtain ⟨p,side,x,location,hit,exit⟩:=fork
   have cut:=literal_boundary_mem_cuts S c.a c.b (p++[!side]) exit.1 exit.2.1 exit.2.2.1 exit.2.2.2
   rcases casesCut (p++[!side]) cut with eqBad|eqSingleton
   · have choices:x=c.a ∨ x=c.b := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.contains_iff_mem.mp hit)
     rcases choices with rfl|rfl
     · exact ⟨U,p,side,c.a,c.b,Or.inl ⟨rfl,rfl⟩,badLocation,eqBad.symm,location⟩
     · exact ⟨U,p,side,c.b,c.a,Or.inr ⟨rfl,rfl⟩,badLocation,eqBad.symm,location⟩
   · have child:=endpointForkTree_child S p side x U location
     have leaf:subtree S (p++[!side])=some (.leaf bad.c) := by
      rw [eqSingleton];exact facts.2.2.2.2
     have Uleaf:U=.leaf bad.c:=Option.some.inj (child.symm.trans leaf)
     have cherry:HasCherry x bad.c S := by
      rw [Uleaf] at location
      exact endpointForkTree_cherry S p side x bad.c location
     have terminal:EndpointTerminal [c.a,c.b] S (minimalVertices [c.a,c.b] S) :=
      ⟨x,bad.c,cherry,hit,Or.inr ⟨p++[!side],exit.1,exit.2.1,exit.2.2.1,exit.2.2.2,leaf⟩⟩
     exact False.elim (actual_terminal_impossible T S c d proper early terminal)

theorem selectFinal_remaining_facts (T S : Tree) (a b : Nat) (bad : BadSelection) (z : BoundarySelection)
 (pick:selectFinal T S a b=some (.remaining bad z)) :
 selectLocal T S a b=some .remaining ∧ selectBad T S a b=some bad ∧
 selectBoundary T (subtreeLabels S bad.badArc) bad.c=some z := by
 cases localPick:selectLocal T S a b with
 | none => rw [selectFinal,localPick] at pick;cases pick
 | some s =>
  cases s with
  | large e => rw [selectFinal,localPick] at pick;cases pick
  | two x => rw [selectFinal,localPick] at pick;cases pick
  | outside x => rw [selectFinal,localPick] at pick;cases pick
  | remaining =>
   rw [selectFinal,localPick] at pick
   cases badPick:selectBad T S a b with
   | none => rw [badPick] at pick;cases pick
   | some actualBad =>
    rw [badPick] at pick
    change (selectBoundary T (subtreeLabels S actualBad.badArc) actualBad.c).bind _=some (FinalSelection.remaining bad z) at pick
    cases boundaryPick:selectBoundary T (subtreeLabels S actualBad.badArc) actualBad.c with
    | none => rw [boundaryPick] at pick;cases pick
    | some actualZ =>
     rw [boundaryPick] at pick
     change some (FinalSelection.remaining actualBad actualZ)=some (FinalSelection.remaining bad z) at pick
     cases pick
     exact ⟨rfl,rfl,boundaryPick⟩

theorem actual_second_endpoint_fork (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃U p side a b,(a=c.a ∧ b=c.b ∨ a=c.b ∧ b=c.a) ∧
  subtree S bad.badArc=some U ∧ bad.badArc=p++[!side] ∧
  subtree S p=some (endpointForkTree side a U) :=
 actual_selected_bad_endpoint_fork T S c d bad proper early
  (selectFinal_remaining_facts T S c.a c.b bad (.second u v) pick).2.1

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.subtree_append_local
#print axioms PaidBuilderAuthor.subtree_append_local
#check @PaidBuilderAuthor.endpointForkTree_child
#print axioms PaidBuilderAuthor.endpointForkTree_child
#check @PaidBuilderAuthor.subtree_cherry_local
#print axioms PaidBuilderAuthor.subtree_cherry_local
#check @PaidBuilderAuthor.endpointForkTree_cherry
#print axioms PaidBuilderAuthor.endpointForkTree_cherry
#check @PaidBuilderAuthor.actual_terminal_impossible
#print axioms PaidBuilderAuthor.actual_terminal_impossible
#check @PaidBuilderAuthor.selected_bad_cut_cases
#print axioms PaidBuilderAuthor.selected_bad_cut_cases
#check @PaidBuilderAuthor.actual_selected_bad_endpoint_fork
#print axioms PaidBuilderAuthor.actual_selected_bad_endpoint_fork
#check @PaidBuilderAuthor.selectFinal_remaining_facts
#print axioms PaidBuilderAuthor.selectFinal_remaining_facts
#check @PaidBuilderAuthor.actual_second_endpoint_fork
#print axioms PaidBuilderAuthor.actual_second_endpoint_fork
