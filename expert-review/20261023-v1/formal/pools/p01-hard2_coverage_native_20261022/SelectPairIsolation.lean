import LiteralOverlap
open RMAF VertexGeometry
namespace ContactedHard2Overlap

theorem repeated_common_none (xs ys : List RMAF.Vertex)
 (h : findCommon xs ys ys=none) : ∀v,v∈xs→v∉ys := by
 induction xs with
 | nil => simp
 | cons a tail ih =>
  simp only [findCommon,Bool.and_self] at h
  cases hc : ys.contains a with
  | false =>
   simp only [hc,Bool.false_eq_true,ite_false] at h
   intro v hv hmy
   rcases List.mem_cons.mp hv with eq|inside
   · subst v
     have yes : ys.contains a=true := List.contains_iff_mem.mpr hmy
     rw [hc] at yes
     cases yes
   · exact ih h v inside hmy
  | true => simp only [hc,ite_true] at h;cases h

theorem overlap_none_clear (T : Tree) (A B : List Nat) (h : overlap T A B=none) : Clear T A B := by
 exact repeated_common_none _ _ h

theorem isolated_pair_order (T : Tree) (A B C : List Nat) (o p : Order) (choice : PairGeometry.Choice)
 (h : isolated T A B C o=some (.pair p choice)) : o=p := by
 unfold isolated at h
 cases pick : PairGeometry.choose T (first o A B C) (second o A B C) with
 | none => simp only [pick,Option.map_none] at h;cases h
 | some w =>
  simp only [pick,Option.map_some,Option.some.injEq,Result.pair.injEq] at h
  exact h.1

theorem chain_not_pair (T : Tree) (A B C : List Nat) (o p : Order) (v w : RMAF.Vertex) (choice : PairGeometry.Choice) :
 chain T A B C o v w≠.pair p choice := by
 unfold chain
 split <;> intro h <;> cases h

theorem select_pair_isolation (T : Tree) (A B C : List Nat) (o : Order) (choice : PairGeometry.Choice)
 (picked : select T A B C=some (.pair o choice)) :
 Clear T (first o A B C) (third o A B C) ∧ Clear T (second o A B C) (third o A B C) := by
 cases hab : overlap T A B with
 | none =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none => simp only [select,hab,hbc,hac] at picked;cases picked
   | some v =>
    have iso : isolated T A B C .acb=some (.pair o choice) := by simpa only [select,hab,hbc,hac] using picked
    have eq:=isolated_pair_order T A B C .acb o choice iso
    subst o
    exact ⟨overlap_none_clear T A B hab,(RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T B C hbc)⟩
  | some w =>
   cases hac : overlap T A C with
   | none =>
    have iso : isolated T A B C .bca=some (.pair o choice) := by simpa only [select,hab,hbc,hac] using picked
    have eq:=isolated_pair_order T A B C .bca o choice iso
    subst o
    exact ⟨(RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T A B hab),
      (RestrictionBridge.clear_symm _ _).2 (overlap_none_clear T A C hac)⟩
   | some v =>
    have eq : chain T A B C .acb v w=.pair o choice := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    exact False.elim (chain_not_pair T A B C .acb o v w choice eq)
 | some v =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none =>
    have iso : isolated T A B C .abc=some (.pair o choice) := by simpa only [select,hab,hbc,hac] using picked
    have eq:=isolated_pair_order T A B C .abc o choice iso
    subst o
    exact ⟨overlap_none_clear T A C hac,overlap_none_clear T B C hbc⟩
   | some w =>
    have eq : chain T A B C .bac v w=.pair o choice := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    exact False.elim (chain_not_pair T A B C .bac o v w choice eq)
  | some w =>
   cases hac : overlap T A C with
   | none =>
    have eq : chain T A B C .abc v w=.pair o choice := Option.some.inj (by simpa only [select,hab,hbc,hac] using picked)
    exact False.elim (chain_not_pair T A B C .abc o v w choice eq)
   | some z =>
    simp only [select,hab,hbc,hac] at picked
    cases triple : findCommon (minimalVertices A T) (minimalVertices B T) (minimalVertices C T) with
    | none => simp only [triple,Option.map_none] at picked;cases picked
    | some r => simp only [triple,Option.map_some] at picked;cases picked

end ContactedHard2Overlap

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.repeated_common_none
#print axioms ContactedHard2Overlap.repeated_common_none
#check @ContactedHard2Overlap.overlap_none_clear
#print axioms ContactedHard2Overlap.overlap_none_clear
#check @ContactedHard2Overlap.isolated_pair_order
#print axioms ContactedHard2Overlap.isolated_pair_order
#check @ContactedHard2Overlap.chain_not_pair
#print axioms ContactedHard2Overlap.chain_not_pair
#check @ContactedHard2Overlap.select_pair_isolation
#print axioms ContactedHard2Overlap.select_pair_isolation
