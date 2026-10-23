import AdmittedSourceSizes
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification

theorem two_good_pendant_exists (T S : Tree) (a b : Nat)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2) :
 ∃e,e∈cuts S a b ∧ restrictionAgrees T S (subtreeLabels S e)=true := by
 classical
 by_cases witness : ∃e,e∈cuts S a b ∧ restrictionAgrees T S (subtreeLabels S e)=true
 · exact witness
 · have empty : ((cuts S a b).map (subtreeLabels S)).filter (restrictionAgrees T S)=[] := by
    apply List.filter_eq_nil_iff.mpr
    intro B member good
    obtain ⟨e,he,eq⟩:=List.mem_map.mp member
    subst B
    exact witness ⟨e,he,good⟩
   change ((((cuts S a b).map (subtreeLabels S))++[coreLabels S a b]).filter (restrictionAgrees T S)).length=2 at two
   rw [List.filter_append,empty,List.nil_append] at two
   cases goodCore : restrictionAgrees T S (coreLabels S a b) <;>
    simp only [List.filter_cons,goodCore,List.filter_nil,List.length_cons,List.length_nil,
     Bool.false_eq_true,ite_false,ite_true] at two <;> omega

theorem remaining_good_singleton_exists (T S : Tree) (a b : Nat)
 (remaining : selectLocal T S a b=some .remaining)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2) :
 ∃e x,e∈cuts S a b ∧ restrictionAgrees T S (subtreeLabels S e)=true ∧
 subtree S e=some (.leaf x) := by
 have localFacts:=(selectLocal_remaining_iff T S a b).mp remaining
 obtain ⟨e,he,good⟩:=two_good_pendant_exists T S a b two
 obtain ⟨x,leaf⟩:=remaining_good_cut_is_leaf T S a b localFacts.2.1 localFacts.2.2.1 e he good
 exact ⟨e,x,he,good,leaf⟩

theorem remaining_bad_witness_if_bad_cut (T S : Tree) (a b : Nat)
 (remaining : selectLocal T S a b=some .remaining)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2)
 (badExists : ∃e,e∈cuts S a b ∧ restrictionAgrees T S (subtreeLabels S e)=false) :
 ∃d,selectBad T S a b=some d := by
 obtain ⟨e,he,bad⟩:=badExists
 obtain ⟨f,c,hf,good,leaf⟩:=remaining_good_singleton_exists T S a b remaining two
 have neq : e≠f := by
  intro eq
  subst e
  rw [good] at bad
  cases bad
 exact selectBad_available T S a b e f c he hf neq bad leaf

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.two_good_pendant_exists
#print axioms AdmittedRule5Author.two_good_pendant_exists
#check @AdmittedRule5Author.remaining_good_singleton_exists
#print axioms AdmittedRule5Author.remaining_good_singleton_exists
#check @AdmittedRule5Author.remaining_bad_witness_if_bad_cut
#print axioms AdmittedRule5Author.remaining_bad_witness_if_bad_cut
