import PaidTargetProps
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap AdmittedRule5Author
open Universal233.Case322Extraction Universal233.Rule5PaidSelector

theorem find_some_of_member {α : Type} (L : List α) (P : α→Bool) (x : α)
 (member:x∈L) (hit:P x=true) : ∃y,L.find? P=some y ∧ P y=true := by
 induction L with
 | nil => cases member
 | cons a tail ih =>
  cases atA:P a with
  | true => exact ⟨a,by simp only [List.find?,atA,ite_true],atA⟩
  | false =>
   have tailMem:x∈tail := by
    rcases List.mem_cons.mp member with eq|rest
    · rw [eq,atA] at hit;cases hit
    · exact rest
   obtain ⟨y,pick,good⟩:=ih tailMem
   exact ⟨y,by simpa only [List.find?,atA,ite_false] using pick,good⟩

theorem literal_leaf_address_available (T : Tree) (a : Nat) (aT:a∈leaves T) :
 ∃q,leafAddress? T a=some q ∧ LeafAt T q a := by
 obtain ⟨w,leaf⟩:=CutRealization.leaf_exists aT
 have wm:w∈Universal233.HardParent.vertices T := (vertices_correct T w).mpr ⟨_,leaf⟩
 obtain ⟨q,pick,hit⟩:=find_some_of_member (Universal233.HardParent.vertices T)
  (fun v=>decide (LeafAt T v a)) w wm (decide_eq_true leaf)
 exact ⟨q,pick,of_decide_eq_true hit⟩

theorem literal_build_one_available (T S : Tree) (a b : Nat) (bad : BadSelection) (u v : Vertex)
 (R : BottomData) (C : Tree) (qa ub : Vertex)
 (hn:(leaves T).Nodup) (Clocation:subtree T v=some C)
 (props:LiteralProps T S a b bad u v R C qa ub) :
 ∃G,buildOne T S a b bad u v R=some G := by
 have aT:=Integration.leafAt_label T qa R.a props.2.2.2.2.2.2.2.1
 have bT:=Integration.leafAt_label T ub R.b props.2.2.2.2.2.2.2.2.1
 obtain ⟨qa',apick,aleaf⟩:=literal_leaf_address_available T R.a aT
 obtain ⟨ub',bpick,bleaf⟩:=literal_leaf_address_available T R.b bT
 have aq:qa'=qa:=CutRealization.leaf_unique hn aleaf props.2.2.2.2.2.2.2.1
 have bq:ub'=ub:=CutRealization.leaf_unique hn bleaf props.2.2.2.2.2.2.2.2.1
 subst qa';subst ub'
 unfold buildOne
 split
 next C' qa' ub' hC ha hb =>
  have eqC:C'=C:=Option.some.inj (hC.symm.trans Clocation)
  have eqA:qa'=qa:=Option.some.inj (ha.symm.trans apick)
  have eqB:ub'=ub:=Option.some.inj (hb.symm.trans bpick)
  subst C';subst qa';subst ub'
  rw [dif_pos props]
  exact ⟨_,rfl⟩
 next impossible =>
  exact False.elim (impossible C qa ub Clocation apick bpick)

theorem find_some_map_of_member {α β : Type} (L : List α) (F : α→Option β) (x : α) (y : β)
 (member:x∈L) (hit:F x=some y) : ∃z,L.findSome? F=some z := by
 induction L with
 | nil => cases member
 | cons a tail ih =>
  cases atA:F a with
  | some z => exact ⟨z,by simp only [List.findSome?,atA]⟩
  | none =>
   have tailMem:x∈tail := by
    rcases List.mem_cons.mp member with eq|rest
    · rw [eq,atA] at hit;cases hit
    · exact rest
   obtain ⟨z,pick⟩:=ih tailMem
   exact ⟨z,by simpa only [List.findSome?,atA] using pick⟩

theorem actual_second_paid_builder (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (graph:runHard2 T S c=some .disjoint)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃G,buildForSecond T S c.a c.b bad u v=some G := by
 obtain ⟨R,Rmem,C,qa,ub,Clocation,props⟩:=actual_second_literal_props T S c d bad u v proper early graph pick
 have priority:=actual_rule4_priority_closed T S c d proper early
 obtain ⟨G,built⟩:=literal_build_one_available T S c.a c.b bad u v R C qa ub priority.1 Clocation props
 exact find_some_map_of_member (rows S c.a c.b bad.c) (buildOne T S c.a c.b bad u v) R G Rmem built

theorem paid_builder_contract : PaidBuilderContract := by
 intro T S c d bad u v proper _pretest early graph _two pick
 exact actual_second_paid_builder T S c d bad u v proper early graph pick

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.find_some_of_member
#print axioms PaidBuilderAuthor.find_some_of_member
#check @PaidBuilderAuthor.literal_leaf_address_available
#print axioms PaidBuilderAuthor.literal_leaf_address_available
#check @PaidBuilderAuthor.literal_build_one_available
#print axioms PaidBuilderAuthor.literal_build_one_available
#check @PaidBuilderAuthor.find_some_map_of_member
#print axioms PaidBuilderAuthor.find_some_map_of_member
#check @PaidBuilderAuthor.actual_second_paid_builder
#print axioms PaidBuilderAuthor.actual_second_paid_builder
#check @PaidBuilderAuthor.paid_builder_contract
#print axioms PaidBuilderAuthor.paid_builder_contract
