import AdmittedGuard
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification

theorem selectLocal_available (T S : Tree) (a b : Nat)
 (guard : admitted T S a b=true) : ∃s,selectLocal T S a b=some s := by
 unfold selectLocal
 rw [guard]
 cases selectLarge T S a b with
 | some e => exact ⟨.large e,rfl⟩
 | none =>
  cases selectSizeTwo T S a b with
  | some c => exact ⟨.two c,rfl⟩
  | none =>
   cases selectOutside T S a b with
   | some c => exact ⟨.outside c,rfl⟩
   | none => exact ⟨.remaining,rfl⟩

theorem selectLocal_remaining_iff (T S : Tree) (a b : Nat) :
 selectLocal T S a b=some .remaining ↔
 admitted T S a b=true ∧ selectLarge T S a b=none ∧
 selectSizeTwo T S a b=none ∧ selectOutside T S a b=none := by
 unfold selectLocal
 cases admitted T S a b <;> cases selectLarge T S a b <;>
  cases selectSizeTwo T S a b <;> cases selectOutside T S a b <;>
  simp only [Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,
   reduceCtorEq,false_and,true_and,
   and_self]

theorem selectBoundary_available_iff (T : Tree) (X : List Nat) (c : Nat) :
 (∃z,selectBoundary T X c=some z) ↔ (incident T X).length=1 ∨ (incident T X).length=2 := by
 unfold selectBoundary
 cases incident T X with
 | nil => simp only [List.length_nil,reduceCtorEq,Nat.zero_ne_add_one,or_self,exists_false]
 | cons q rest =>
  cases rest with
  | nil => exact ⟨fun _=>Or.inl rfl,fun _=>⟨.one q,rfl⟩⟩
  | cons r tail =>
   cases tail with
   | nil =>
    constructor
    · intro _;exact Or.inr rfl
    · intro _
      dsimp only
      repeat' first | exact ⟨_,rfl⟩ | split
   | cons s more =>
    constructor
    · rintro ⟨z,bad⟩;cases bad
    · intro bad
      simp only [List.length_cons] at bad
      omega

theorem selectFinal_refusal_iff (T S : Tree) (a b : Nat)
 (guard : admitted T S a b=true) :
 selectFinal T S a b=none ↔
 selectLocal T S a b=some .remaining ∧
 (selectBad T S a b=none ∨ ∃d,selectBad T S a b=some d ∧
  selectBoundary T (subtreeLabels S d.badArc) d.c=none) := by
 obtain ⟨s,picked⟩:=selectLocal_available T S a b guard
 rw [selectFinal,picked]
 cases s with
 | large e => simp only [Option.some.injEq,reduceCtorEq,false_and]
 | two c => simp only [Option.some.injEq,reduceCtorEq,false_and]
 | outside c => simp only [Option.some.injEq,reduceCtorEq,false_and]
 | remaining =>
  cases bad:selectBad T S a b with
  | none =>
    change (none:Option FinalSelection)=none ↔ _
    exact ⟨fun _=>⟨rfl,Or.inl rfl⟩,fun _=>rfl⟩
  | some d =>
   cases boundary:selectBoundary T (subtreeLabels S d.badArc) d.c with
   | none =>
    constructor
    · intro _;exact ⟨rfl,Or.inr ⟨d,rfl,boundary⟩⟩
    · intro _
      change (selectBoundary T (subtreeLabels S d.badArc) d.c).bind _=none
      rw [boundary]
      rfl
   | some z =>
    constructor
    · intro h
      change (selectBoundary T (subtreeLabels S d.badArc) d.c).bind _=none at h
      rw [boundary] at h
      cases h
    · rintro ⟨_,noBad|⟨e,same,missing⟩⟩
      · cases noBad
      · cases same
        rw [boundary] at missing
        cases missing

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.selectLocal_available
#print axioms AdmittedRule5Author.selectLocal_available
#check @AdmittedRule5Author.selectLocal_remaining_iff
#print axioms AdmittedRule5Author.selectLocal_remaining_iff
#check @AdmittedRule5Author.selectBoundary_available_iff
#print axioms AdmittedRule5Author.selectBoundary_available_iff
#check @AdmittedRule5Author.selectFinal_refusal_iff
#print axioms AdmittedRule5Author.selectFinal_refusal_iff
