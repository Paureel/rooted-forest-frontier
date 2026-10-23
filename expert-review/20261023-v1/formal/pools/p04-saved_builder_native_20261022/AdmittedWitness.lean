import AdmittedSource
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent

theorem hasCherry_ne {T : Tree} {a b : Nat} (h : HasCherry a b T) :
 (leaves T).Nodup→a≠b := by
 induction h with
 | here =>
  intro hn
  simpa only [leaves,List.cons_append,List.nil_append,List.nodup_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_true] using hn
 | swap =>
  intro hn
  have ne : b≠a:=by
   simpa only [leaves,List.cons_append,List.nil_append,List.nodup_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,not_false_eq_true,and_true] using hn
  exact Ne.symm ne
 | left h ih =>
  intro hn
  apply ih
  exact (List.nodup_append.mp hn).1
 | right h ih =>
  intro hn
  apply ih
  exact (List.nodup_append.mp hn).2.1

theorem two_list_perm_member {α : Type} (xs : List α) (q : α)
 (len : xs.length=2) (member : q∈xs) : ∃r,xs.Perm [q,r] := by
 cases xs with
 | nil => simp only [List.length_nil] at len;omega
 | cons a tail =>
  cases tail with
  | nil => simp only [List.length_cons,List.length_nil] at len;omega
  | cons b tail =>
   cases tail with
   | nil =>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with eq|eq
    · subst q;exact ⟨b,List.Perm.refl _⟩
    · subst q;exact ⟨a,List.Perm.swap _ _ []⟩
   | cons c cs => simp only [List.length_cons] at len;omega

theorem singleton_raw_guard {T S : Tree} (candidate : Candidate)
 (member : candidate∈candidates T S) (properT : (leaves T).Nodup)
 (q r : RMAF.Vertex) (x : Nat)
 (order : candidate.originalCuts.Perm [q,r])
 (singleton : subtreeLabels S q=[x]) (mate : hasCherry S candidate.a x=true) :
 Rule4.LocalGuard T S ⟨candidate.a,candidate.b,x,q,r⟩ := by
 have facts:=selected_candidate_source T S candidate member
 refine ⟨hasCherry_bool_ordered T candidate.a candidate.b facts.1,
  hasCherry_bool_ordered S candidate.a x mate,hasCherry_ne (hasCherry_bool_prop T candidate.a candidate.b facts.1) properT,?_,singleton⟩
 change (pendantOriginal S candidate.a candidate.b).Perm [q,r]
 rw [facts.2] at order
 exact order
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.hasCherry_ne
#print axioms AdmittedRule5Author.hasCherry_ne
#check @AdmittedRule5Author.two_list_perm_member
#print axioms AdmittedRule5Author.two_list_perm_member
#check @AdmittedRule5Author.singleton_raw_guard
#print axioms AdmittedRule5Author.singleton_raw_guard
