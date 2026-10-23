import ELOuter
namespace OrdinaryDispatch.EarlyLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence

/-- Refusal charges every raw candidate, before and without LocalGuard acceptance. -/
theorem meterFirstChoice_none_checks (T S : Tree) (hp : Rule4.Priority T S)
 (xs : List Rule4.RawChoice) (noneValue : (meterFirstChoice T S hp xs).value=none) :
 (meterFirstChoice T S hp xs).checks=xs.map (fun x=>(x,false)) := by
 induction xs with
 | nil=>rfl
 | cons x xs ih=>
  simp only [meterFirstChoice] at noneValue ⊢
  split at noneValue ⊢
  · contradiction
  · simp only [ChoiceMeasured.value] at noneValue
    simp only [ChoiceMeasured.checks,List.map_cons,ih noneValue]

/-- Public primitive envelope, with literal tree-size premises only. -/
theorem cherry_select_envelope (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterSelect T S).value=CherryBranching.select T S ∧
 (meterSelect T S).work≤2048*(N+1)^5 :=
 ⟨meterSelect_value T S,meterSelect_bound T S N tn sn⟩

/-- Public primitive Rule4 envelope. The raw head caps are proved from
rawChoices membership, not supplied by a successful guard. -/
theorem rule4_select_envelope (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (meterRule4Select T S).value=Rule4.select T S ∧
 (meterRule4Select T S).work≤262144*(N+1)^6 :=
 ⟨meterRule4Select_value T S,meterRule4Select_bound T S N tn sn⟩

/-- Calls in both orientations have the same uniform envelope. -/
theorem earlier_clear_primitive_envelopes (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 ((meterSelect T S).work+(meterSelect S T).work)+
 ((meterRule4Select T S).work+(meterRule4Select S T).work)≤1048576*(N+1)^6 := by
 have f:=cap_lift N 2048 5 6 _ (meterSelect_bound T S N tn sn) (by decide)
 have r:=cap_lift N 2048 5 6 _ (meterSelect_bound S T N sn tn) (by decide)
 have a:=meterRule4Select_bound T S N tn sn
 have b:=meterRule4Select_bound S T N sn tn
 omega
end OrdinaryDispatch.EarlyLocalWork
