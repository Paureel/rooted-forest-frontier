import AdmittedRemainingPartition
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch

-- This is a reduction of a possible scan refusal, not a proof of infeasibility.
theorem remaining_no_bad_every_cut_good (T S : Tree) (a b : Nat)
 (remaining : selectLocal T S a b=some .remaining)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2)
 (missing : selectBad T S a b=none) :
 ∀e∈cuts S a b,restrictionAgrees T S (subtreeLabels S e)=true := by
 intro e member
 cases good:restrictionAgrees T S (subtreeLabels S e) with
 | true => rfl
 | false =>
  obtain ⟨d,pick⟩:=remaining_bad_witness_if_bad_cut T S a b remaining two ⟨e,member,good⟩
  rw [missing] at pick
  cases pick

theorem remaining_no_bad_every_cut_leaf (T S : Tree) (a b : Nat)
 (remaining : selectLocal T S a b=some .remaining)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2)
 (missing : selectBad T S a b=none) :
 ∀e∈cuts S a b,∃x,subtree S e=some (.leaf x) := by
 have selectors:=(selectLocal_remaining_iff T S a b).mp remaining
 intro e member
 exact remaining_good_cut_is_leaf T S a b selectors.2.1 selectors.2.2.1 e member
  (remaining_no_bad_every_cut_good T S a b remaining two missing e member)

theorem remaining_no_bad_core_bad (T S : Tree) (a b : Nat)
 (len : (cuts S a b).length=2)
 (remaining : selectLocal T S a b=some .remaining)
 (two : ((pendantPartition S a b).filter (restrictionAgrees T S)).length=2)
 (missing : selectBad T S a b=none) :
 restrictionAgrees T S (coreLabels S a b)=false := by
 have allGood:=remaining_no_bad_every_cut_good T S a b remaining two missing
 have unchanged:(((cuts S a b).map (subtreeLabels S)).filter (restrictionAgrees T S))=
  (cuts S a b).map (subtreeLabels S) := by
  apply List.filter_eq_self.mpr
  intro B member
  obtain ⟨e,he,eq⟩:=List.mem_map.mp member
  subst B
  exact allGood e he
 change ((((cuts S a b).map (subtreeLabels S))++[coreLabels S a b]).filter
  (restrictionAgrees T S)).length=2 at two
 rw [List.filter_append,unchanged,List.length_append,List.length_map,len] at two
 cases core:restrictionAgrees T S (coreLabels S a b) with
 | false => rfl
 | true =>
  simp only [List.filter_cons,List.filter_nil,core,ite_true,List.length_cons,List.length_nil] at two
  omega

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.remaining_no_bad_every_cut_good
#print axioms AdmittedRule5Author.remaining_no_bad_every_cut_good
#check @AdmittedRule5Author.remaining_no_bad_every_cut_leaf
#print axioms AdmittedRule5Author.remaining_no_bad_every_cut_leaf
#check @AdmittedRule5Author.remaining_no_bad_core_bad
#print axioms AdmittedRule5Author.remaining_no_bad_core_bad
