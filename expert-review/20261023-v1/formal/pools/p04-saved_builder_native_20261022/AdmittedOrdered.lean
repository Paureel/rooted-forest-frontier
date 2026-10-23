import AdmittedRoute
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent

theorem ordered_hasCherry (T : Tree) (a b : Nat)
 (member : (a,b)∈Rule4.orderedCherries T) : HasCherry a b T := by
 induction T with
 | leaf x => simp only [Rule4.orderedCherries,List.not_mem_nil] at member
 | node l r ihl ihr =>
  simp only [Rule4.orderedCherries,List.mem_append] at member
  rcases member with (atRoot|left)|right
  · cases l <;> cases r <;> simp only [List.not_mem_nil] at atRoot
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at atRoot
    rcases atRoot with ⟨hx,hy⟩|⟨hx,hy⟩
    · subst a;subst b;exact .here
    · subst a;subst b;exact .swap
  · exact .left (ihl left)
  · exact .right (ihr right)

theorem hasCherry_original_tuple {T : Tree} {a b : Nat} (h : HasCherry a b T) :
 (∃p,(p,a,b)∈cherries T) ∨ (∃p,(p,b,a)∈cherries T) := by
 induction h with
 | here => exact Or.inl ⟨[],by simp only [cherries,List.mem_singleton]⟩
 | swap => exact Or.inr ⟨[],by simp only [cherries,List.mem_singleton]⟩
 | @left l r h ih =>
  cases l with
  | leaf x => cases h
  | node l1 l2 =>
   rcases ih with ⟨p,hm⟩|⟨p,hm⟩
   · exact Or.inl ⟨false::p,by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨(p,a,b),hm,rfl⟩⟩
   · exact Or.inr ⟨false::p,by
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨(p,b,a),hm,rfl⟩⟩
 | @right l r h ih =>
  cases r with
  | leaf x => cases h
  | node r1 r2 =>
   cases l <;> rcases ih with ⟨p,hm⟩|⟨p,hm⟩
   all_goals first
    | exact Or.inl ⟨true::p,by
       apply List.mem_append_right
       exact List.mem_map.mpr ⟨(p,a,b),hm,rfl⟩⟩
    | exact Or.inr ⟨true::p,by
       apply List.mem_append_right
       exact List.mem_map.mpr ⟨(p,b,a),hm,rfl⟩⟩

theorem earlier_clear_cherry_length (T S : Tree) (a b : Nat)
 (clear : earlierClear T S=true) (cherry : HasCherry a b T) :
 (pendantOriginal S a b).length=2 := by
 have get : ∀p x y,(p,x,y)∈cherries T→(pendantOriginal S x y).length=2 := by
  intro p x y hm
  have member : (⟨p,x,y,cuts S x y⟩:Candidate)∈candidates T S :=
   List.mem_map.mpr ⟨(p,x,y),hm,rfl⟩
  exact beq_iff_eq.mp ((List.all_eq_true.mp clear) _ member)
 rcases hasCherry_original_tuple cherry with ⟨p,hm⟩|⟨p,hm⟩
 · exact get p a b hm
 · rw [pendantOriginal_swap S a b]
   exact get p b a hm

theorem earlier_clear_ordered_length (T S : Tree)
 (clear : earlierClear T S=true) :
 ∀p∈Rule4.orderedCherries T,(pendantOriginal S p.1 p.2).length=2 := by
 intro ⟨a,b⟩ hm
 exact earlier_clear_cherry_length T S a b clear (ordered_hasCherry T a b hm)

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.ordered_hasCherry
#print axioms AdmittedRule5Author.ordered_hasCherry
#check @AdmittedRule5Author.hasCherry_original_tuple
#print axioms AdmittedRule5Author.hasCherry_original_tuple
#check @AdmittedRule5Author.earlier_clear_cherry_length
#print axioms AdmittedRule5Author.earlier_clear_cherry_length
#check @AdmittedRule5Author.earlier_clear_ordered_length
#print axioms AdmittedRule5Author.earlier_clear_ordered_length
