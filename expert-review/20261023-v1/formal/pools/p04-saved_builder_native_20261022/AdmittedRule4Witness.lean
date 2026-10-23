import AdmittedWitness
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent

theorem singleton_raw_guard_swap {T S : Tree} (candidate : Candidate)
 (member : candidate∈candidates T S) (properT : (leaves T).Nodup)
 (q r : RMAF.Vertex) (x : Nat)
 (order : candidate.originalCuts.Perm [q,r])
 (singleton : subtreeLabels S q=[x]) (mate : hasCherry S candidate.b x=true) :
 Rule4.LocalGuard T S ⟨candidate.b,candidate.a,x,q,r⟩ := by
 have facts:=selected_candidate_source T S candidate member
 have original:=hasCherry_bool_prop T candidate.a candidate.b facts.1
 refine ⟨Rule4.orderedCherries_complete (hasCherry_prop_swap original),
  hasCherry_bool_ordered S candidate.b x mate,Ne.symm (hasCherry_ne original properT),?_,singleton⟩
 change (pendantOriginal S candidate.b candidate.a).Perm [q,r]
 rw [pendantOriginal_swap S candidate.b candidate.a]
 rw [facts.2] at order
 exact order

theorem syntactic_rule4_witness (T S : Tree) (properT : (leaves T).Nodup)
 (trigger : rule4 T S=true) : ∃s,Rule4.LocalGuard T S s := by
 obtain ⟨candidate,member,check⟩:=List.any_eq_true.mp trigger
 change (candidate.originalCuts.length==2 && candidate.originalCuts.any (fun q=>match subtreeLabels S q with
  | [x]=>hasCherry S candidate.a x || hasCherry S candidate.b x
  | _=>false))=true at check
 simp only [Bool.and_eq_true,beq_iff_eq] at check
 obtain ⟨q,hq,good⟩:=List.any_eq_true.mp check.2
 change (match subtreeLabels S q with
  | [x]=>hasCherry S candidate.a x || hasCherry S candidate.b x
  | _=>false)=true at good
 split at good
 · rename_i x labels
   obtain ⟨r,order⟩:=two_list_perm_member candidate.originalCuts q check.1 hq
   have choices : hasCherry S candidate.a x=true ∨ hasCherry S candidate.b x=true:=by
    simpa only [Bool.or_eq_true] using good
   rcases choices with forward|reverse
   · exact ⟨⟨candidate.a,candidate.b,x,q,r⟩,singleton_raw_guard candidate member properT q r x order labels forward⟩
   · exact ⟨⟨candidate.b,candidate.a,x,q,r⟩,singleton_raw_guard_swap candidate member properT q r x order labels reverse⟩
 · cases good

theorem selected_rule4_none_syntactic_false (T S : Tree)
 (priority : Rule4.Priority T S) (refused : Rule4.select T S=none) : rule4 T S=false := by
 cases trigger:rule4 T S with
 | false => rfl
 | true =>
  obtain ⟨s,guard⟩:=syntactic_rule4_witness T S priority.1 trigger
  obtain ⟨c,picked⟩:=Rule4.select_complete priority s guard
  rw [refused] at picked
  cases picked
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.singleton_raw_guard_swap
#print axioms AdmittedRule5Author.singleton_raw_guard_swap
#check @AdmittedRule5Author.syntactic_rule4_witness
#print axioms AdmittedRule5Author.syntactic_rule4_witness
#check @AdmittedRule5Author.selected_rule4_none_syntactic_false
#print axioms AdmittedRule5Author.selected_rule4_none_syntactic_false
