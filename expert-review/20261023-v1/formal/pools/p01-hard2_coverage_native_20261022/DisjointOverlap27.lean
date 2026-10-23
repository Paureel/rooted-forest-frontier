import DisjointPriority22
open RMAF Universal233 CherryBranching OrdinaryDispatch
namespace FreshLiteralDisjoint
theorem run_disjoint_two {T S : Tree} {c : Candidate}
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint) :
 ∃p r,c.originalCuts=[p,r] ∧
   Hard2Overlap.select T (PaidAssembly.leftParent S p) (PaidAssembly.rightParent S r)
     (PaidAssembly.rootParent S p r)=some .disjoint := by
 unfold Hard2Overlap.runHard2 at picked
 cases hc : c.originalCuts with
 | nil => rw [hc] at picked; cases picked
 | cons p rest =>
  cases rest with
  | nil => rw [hc] at picked; cases picked
  | cons r rest =>
   cases rest with
   | nil =>
    refine ⟨p,r,rfl,?_⟩
    rw [hc] at picked
    exact picked
   | cons x xs => rw [hc] at picked; cases picked

theorem disjoint_empty_overlaps (T : Tree) (A B C : List Nat)
 (picked : Hard2Overlap.select T A B C=some .disjoint) :
 Hard2Overlap.overlap T A B=none ∧ Hard2Overlap.overlap T B C=none ∧
 Hard2Overlap.overlap T A C=none := by
 cases hab : Hard2Overlap.overlap T A B <;>
 cases hbc : Hard2Overlap.overlap T B C <;>
 cases hac : Hard2Overlap.overlap T A C
 all_goals simp only [Hard2Overlap.select,hab,hbc,hac,Hard2Overlap.select.match_1] at picked
 · exact ⟨rfl,rfl,rfl⟩
 all_goals simp only [Hard2Overlap.chain,Hard2Overlap.isolated,Option.map_eq_some_iff,Option.some.injEq] at picked
 all_goals first
 | (split at picked <;> cases picked)
 | (obtain ⟨v,hv,he⟩:=picked;cases he)
end FreshLiteralDisjoint

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.run_disjoint_two
#print axioms FreshLiteralDisjoint.run_disjoint_two
#check @FreshLiteralDisjoint.disjoint_empty_overlaps
#print axioms FreshLiteralDisjoint.disjoint_empty_overlaps
