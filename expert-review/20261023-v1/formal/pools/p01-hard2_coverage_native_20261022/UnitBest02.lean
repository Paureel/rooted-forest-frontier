import UnitSelection03
namespace UnitPaidCombination
open RMAF Universal233 Universal233.CherryBranching OrdinaryDispatch

theorem best_sound_fresh {α : Type} (cost : α→Nat) (valid : α→Bool)
    (xs : List α) (G : α) (h : best cost valid xs=some G) : G∈xs ∧ valid G=true := by
 induction xs generalizing G with
 | nil => simp [best] at h
 | cons a xs ih =>
   cases va : valid a with
   | false =>
     have tail : best cost valid xs=some G := by simpa [best,va] using h
     have inside:=ih G tail
     exact ⟨by simp [inside.1],inside.2⟩
   | true =>
     cases hb : best cost valid xs with
     | none =>
       have eq : a=G := by simpa [best,va,hb] using h
       subst G
       exact ⟨by simp,va⟩
     | some b =>
       by_cases ab : cost a≤cost b
       · have eq : a=G := by simpa [best,va,hb,ab] using h
         subst G
         exact ⟨by simp,va⟩
       · have eq : b=G := by simpa [best,va,hb,ab] using h
         subst G
         have inside:=ih b hb
         exact ⟨by simp [inside.1],inside.2⟩

theorem best_exists_le_fresh {α : Type} (cost : α→Nat) (valid : α→Bool)
    (xs : List α) (F : α) (hm : F∈xs) (hv : valid F=true) :
    ∃ G,best cost valid xs=some G ∧ valid G=true ∧ cost G≤cost F := by
 induction xs with
 | nil => simp at hm
 | cons a xs ih =>
   rcases List.mem_cons.mp hm with eq|hm
   · subst F
     cases hb : best cost valid xs with
     | none => exact ⟨a,by simp [best,hv,hb],hv,Nat.le_refl _⟩
     | some b =>
       have vb:=(best_sound_fresh cost valid xs b hb).2
       by_cases ab : cost a≤cost b
       · exact ⟨a,by simp [best,hv,hb,ab],hv,Nat.le_refl _⟩
       · exact ⟨b,by simp [best,hv,hb,ab],vb,by omega⟩
   · obtain ⟨b,hb,vb,least⟩:=ih hm
     cases va : valid a with
     | false => exact ⟨b,by simp [best,va,hb],vb,least⟩
     | true =>
       by_cases ab : cost a≤cost b
       · exact ⟨a,by simp [best,va,hb,ab],va,Nat.le_trans ab least⟩
       · exact ⟨b,by simp [best,va,hb,ab],vb,least⟩

theorem best_first_min_fresh {α : Type} (cost : α→Nat) (valid : α→Bool)
    (a : α) (xs : List α) (va : valid a=true)
    (least : ∀ b,b∈xs → cost a≤cost b) : best cost valid (a::xs)=some a := by
 cases hb : best cost valid xs with
 | none => simp [best,va,hb]
 | some b =>
   have hm:=(best_sound_fresh cost valid xs b hb).1
   simp [best,va,hb,least b hm]

theorem run_children_sound_fresh (actual : Hard2Combine.Ordinary) (T S : Tree)
    (q : Nat) (cs : List Child) (G : OrdinaryDispatch.Forest)
    (h : runChildren actual T S q cs=some G) :
    agreement T S G=true ∧ G.length-1≤q := by
 have valid:=(best_sound_fresh List.length (ordinaryAccepted T S q)
   (childAnswers actual T q cs) G h).2
 simpa only [ordinaryAccepted,Bool.and_eq_true,decide_eq_true_eq] using valid

theorem unit_first_tie_fresh (actual : Hard2Combine.Ordinary) (T S : Tree)
    (a b q : Nat) (A B : OrdinaryDispatch.Forest)
    (ha : childCall (forestChild actual T) q (singletonChild S a)=some A)
    (hb : childCall (forestChild actual T) q (singletonChild S b)=some B)
    (va : ordinaryAccepted T S q A=true) (vb : ordinaryAccepted T S q B=true)
    (eq : A.length=B.length) :
    runChildren actual T S q [singletonChild S a,singletonChild S b]=some A := by
 simp [runChildren,childAnswers,ha,hb,best,va,vb,eq]
end UnitPaidCombination

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @UnitPaidCombination.best_sound_fresh
#print axioms UnitPaidCombination.best_sound_fresh
#check @UnitPaidCombination.best_exists_le_fresh
#print axioms UnitPaidCombination.best_exists_le_fresh
#check @UnitPaidCombination.best_first_min_fresh
#print axioms UnitPaidCombination.best_first_min_fresh
#check @UnitPaidCombination.run_children_sound_fresh
#print axioms UnitPaidCombination.run_children_sound_fresh
#check @UnitPaidCombination.unit_first_tie_fresh
#print axioms UnitPaidCombination.unit_first_tie_fresh
