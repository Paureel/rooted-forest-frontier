import Hard2Program
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local

theorem select_hard2_membership_clear (T S : Tree) (c : Candidate)
 (selected : select T S=some (.hard2,c)) :
 c∈candidates T S ∧ earlierClear T S=true := by
 cases h0 : (candidates T S).find? (fun x=>x.originalCuts.isEmpty) with
 | some k => rw [select,h0] at selected;cases selected
 | none =>
  cases h1 : (candidates T S).find? (fun x=>x.originalCuts.length==1) with
  | some k => rw [select,h0,h1] at selected;cases selected
  | none =>
   cases hh : (candidates T S).find? (fun x=>decide (3≤x.originalCuts.length)) with
   | some k => rw [select,h0,h1,hh] at selected;cases selected
   | none =>
    rw [select,h0,h1,hh] at selected
    have clear : earlierClear T S=true := by
     apply List.all_eq_true.mpr
     intro x hx
     have nz: x.originalCuts.length≠0:=by
      intro z
      have empty:=List.length_eq_zero_iff.mp z
      exact (List.find?_eq_none.mp h0 x hx) (by rw [empty];rfl)
     have no1: x.originalCuts.length≠1:=by
      intro z
      exact (List.find?_eq_none.mp h1 x hx) (by rw [z];rfl)
     have no3: ¬3≤x.originalCuts.length:=by
      intro z
      exact (List.find?_eq_none.mp hh x hx) (decide_eq_true z)
     apply beq_iff_eq.mpr
     omega
    refine ⟨?_,clear⟩
    cases head : (candidates T S).head? with
    | none => rw [head] at selected;cases selected
    | some k =>
     rw [head] at selected
     change some (Priority.hard2,k)=some (Priority.hard2,c) at selected
     have eq : k=c:=congrArg Prod.snd (Option.some.inj selected)
     subst k
     exact List.mem_of_head? head

theorem selected_candidate_source (T S : Tree) (c : Candidate)
 (member : c∈candidates T S) :
 hasCherry T c.a c.b=true ∧ c.originalCuts=cuts S c.a c.b := by
 obtain ⟨triple,hmem,eq⟩:=List.mem_map.mp member
 rcases triple with ⟨p,a,b⟩
 cases eq
 refine ⟨?_,rfl⟩
 apply List.any_eq_true.mpr
 exact ⟨(p,a,b),hmem,by simp only [beq_self_eq_true,Bool.true_and,Bool.true_or]⟩

theorem proper_to_properPair (T S : Tree) (proper : DepthOne.proper T S=true) :
 properPair T S=true := by
 have h : (decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧ decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 have perm : (leaves T).Perm (leaves S):=of_decide_eq_true h.2
 have ts : (leaves T).all (leaves S).contains=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact List.contains_iff_mem.mpr (perm.mem_iff.mp hx)
 have st : (leaves S).all (leaves T).contains=true := by
  apply List.all_eq_true.mpr
  intro x hx
  exact List.contains_iff_mem.mpr (perm.mem_iff.mpr hx)
 simp only [properPair,Bool.and_eq_true]
 exact ⟨⟨h.1,ts⟩,st⟩
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.select_hard2_membership_clear
#print axioms AdmittedRule5Author.select_hard2_membership_clear
#check @AdmittedRule5Author.selected_candidate_source
#print axioms AdmittedRule5Author.selected_candidate_source
#check @AdmittedRule5Author.proper_to_properPair
#print axioms AdmittedRule5Author.proper_to_properPair
