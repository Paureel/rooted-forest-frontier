import AdmittedClosed
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent Universal233.Rule5Classification Universal233.Rule5FinalClassification

theorem badAt_sound (T S : Tree) (e f : Vertex) (d : BadSelection)
 (picked : badAt T S e f=some d) :
 d.badArc=e ∧ d.singletonArc=f ∧ e≠f ∧
 restrictionAgrees T S (subtreeLabels S e)=false ∧ subtree S f=some (.leaf d.c) := by
 unfold badAt at picked
 split at picked
 · rename_i h
   split at picked
   · cases Option.some.inj picked
     exact ⟨rfl,rfl,h.1,h.2,by assumption⟩
   · cases picked
 · cases picked

theorem badCandidates_sound (T S : Tree) (a b : Nat) (d : BadSelection)
 (member : d∈badCandidates T S a b) :
 d.badArc∈cuts S a b ∧ d.singletonArc∈cuts S a b ∧ d.badArc≠d.singletonArc ∧
 restrictionAgrees T S (subtreeLabels S d.badArc)=false ∧
 subtree S d.singletonArc=some (.leaf d.c) := by
 obtain ⟨e,he,hm⟩:=List.mem_flatMap.mp member
 obtain ⟨f,hf,atPick⟩:=List.mem_filterMap.mp hm
 have facts:=badAt_sound T S e f d atPick
 rcases facts with ⟨de,df,neq,bad,single⟩
 rw [de,df]
 exact ⟨he,hf,neq,bad,single⟩

theorem selectBad_sound (T S : Tree) (a b : Nat) (d : BadSelection)
 (picked : selectBad T S a b=some d) :
 d.badArc∈cuts S a b ∧ d.singletonArc∈cuts S a b ∧ d.badArc≠d.singletonArc ∧
 restrictionAgrees T S (subtreeLabels S d.badArc)=false ∧
 subtree S d.singletonArc=some (.leaf d.c) :=
 badCandidates_sound T S a b d (List.mem_of_head? picked)

theorem selectBad_available (T S : Tree) (a b : Nat) (e f : Vertex) (c : Nat)
 (he : e∈cuts S a b) (hf : f∈cuts S a b) (neq : e≠f)
 (bad : restrictionAgrees T S (subtreeLabels S e)=false)
 (single : subtree S f=some (.leaf c)) : ∃d,selectBad T S a b=some d := by
 have atPick : badAt T S e f=some ⟨e,f,c⟩ := by
  have cond : e≠f ∧ restrictionAgrees T S (subtreeLabels S e)=false:=⟨neq,bad⟩
  rw [badAt,if_pos cond,single]
 have member : (⟨e,f,c⟩:BadSelection)∈badCandidates T S a b :=
  List.mem_flatMap.mpr ⟨e,he,List.mem_filterMap.mpr ⟨f,hf,atPick⟩⟩
 cases head:selectBad T S a b with
 | some d => exact ⟨d,rfl⟩
 | none =>
  have empty : badCandidates T S a b=[]:=List.head?_eq_none_iff.mp head
  rw [empty] at member
  cases member

theorem selectLarge_none_good_small (T S : Tree) (a b : Nat)
 (missing : selectLarge T S a b=none) (e : Vertex)
 (he : e∈cuts S a b) (good : restrictionAgrees T S (subtreeLabels S e)=true) :
 (subtreeLabels S e).length<3 := by
 have empty : largeCandidates T S a b=[]:=List.head?_eq_none_iff.mp missing
 by_cases small : (subtreeLabels S e).length<3
 · exact small
 · have large : 3≤(subtreeLabels S e).length:=by omega
   have member : e∈largeCandidates T S a b :=
    List.mem_filter.mpr ⟨he,by simp only [good,decide_eq_true large,Bool.true_and]⟩
   rw [empty] at member
   cases member

theorem selectSizeTwo_none_no_good_cherry (T S : Tree) (a b : Nat)
 (missing : selectSizeTwo T S a b=none) (e : Vertex) (p q : Nat)
 (he : e∈cuts S a b) (good : restrictionAgrees T S (subtreeLabels S e)=true) :
 subtree S e≠some (.node (.leaf p) (.leaf q)) := by
 intro source
 have atPick : sizeTwoAt T S e=some ⟨e,p,q⟩ := by
  simp only [sizeTwoAt,good,ite_true,source]
 have member : (⟨e,p,q⟩:SizeTwoSelection)∈sizeTwoCandidates T S a b :=
  List.mem_filterMap.mpr ⟨e,he,atPick⟩
 have empty : sizeTwoCandidates T S a b=[]:=List.head?_eq_none_iff.mp missing
 rw [empty] at member
 cases member

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.badAt_sound
#print axioms AdmittedRule5Author.badAt_sound
#check @AdmittedRule5Author.badCandidates_sound
#print axioms AdmittedRule5Author.badCandidates_sound
#check @AdmittedRule5Author.selectBad_sound
#print axioms AdmittedRule5Author.selectBad_sound
#check @AdmittedRule5Author.selectBad_available
#print axioms AdmittedRule5Author.selectBad_available
#check @AdmittedRule5Author.selectLarge_none_good_small
#print axioms AdmittedRule5Author.selectLarge_none_good_small
#check @AdmittedRule5Author.selectSizeTwo_none_no_good_cherry
#print axioms AdmittedRule5Author.selectSizeTwo_none_no_good_cherry
