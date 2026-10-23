import CliqueCompletenessV2
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedHard2Overlap

theorem select_total (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true) :
 ∃out,select T A B C=some out := by
 cases hab : overlap T A B with
 | none =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none => exact ⟨.disjoint,by simp only [select,hab,hbc,hac]⟩
   | some v =>
    obtain ⟨ch,found,_⟩:=isolated_acb_complete T S A B C v proper part hab hbc hac
    exact ⟨_,found⟩
  | some w =>
   cases hac : overlap T A C with
   | none =>
    obtain ⟨ch,found,_⟩:=isolated_bca_complete T S A B C w proper part hab hbc hac
    exact ⟨_,found⟩
   | some v => exact ⟨chain T A B C .acb v w,by simp only [select,hab,hbc,hac]⟩
 | some v =>
  cases hbc : overlap T B C with
  | none =>
   cases hac : overlap T A C with
   | none =>
    obtain ⟨ch,found,_⟩:=isolated_abc_complete T S A B C v proper part hab hbc hac
    exact ⟨_,found⟩
   | some w => exact ⟨chain T A B C .bac v w,by simp only [select,hab,hbc,hac]⟩
  | some w =>
   cases hac : overlap T A C with
   | none => exact ⟨chain T A B C .abc v w,by simp only [select,hab,hbc,hac]⟩
   | some z =>
    obtain ⟨r,found,_,_,_⟩:=clique_search_complete T A B C v w z hab hbc hac
    exact ⟨_,found⟩
end ContactedHard2Overlap
namespace ContactedActualHard2

theorem actual_two_cuts {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) :
 ∃p r,c.originalCuts=[p,r] := by
 have domain:=ContactedHard2.actual_hard2_domain proper selected
 have count:=domain.2.1.2.2
 cases cuts : c.originalCuts with
 | nil => simp only [cuts,List.length_nil] at count;omega
 | cons p tail =>
  cases tail with
  | nil => simp only [cuts,List.length_cons,List.length_nil] at count;omega
  | cons r rest =>
   have zero : rest.length=0 := by simp only [cuts,List.length_cons] at count;omega
   have empty : rest=[] := List.length_eq_zero_iff.1 zero
   subst rest
   exact ⟨p,r,rfl⟩

theorem runHard2_total {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) :
 ∃out,runHard2 T S c=some out := by
 obtain ⟨p,r,shape⟩:=actual_two_cuts proper selected
 have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ (List.Perm.refl _)
 obtain ⟨out,found⟩:=ContactedHard2Overlap.select_total T S _ _ _ proper checks.1
 exact ⟨out,by simpa only [runHard2,shape] using found⟩
end ContactedActualHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.select_total
#print axioms ContactedHard2Overlap.select_total
#check @ContactedActualHard2.actual_two_cuts
#print axioms ContactedActualHard2.actual_two_cuts
#check @ContactedActualHard2.runHard2_total
#print axioms ContactedActualHard2.runHard2_total
