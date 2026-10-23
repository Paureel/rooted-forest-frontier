import DisjointExact
namespace OrdinaryDispatch.DisjointParents
open RMAF Universal233

theorem bad_good_balance (T S : Tree) (P : OrdinaryDispatch.Forest) :
 MafScheduler.badParents T S P+(P.filter (restrictionAgrees T S)).length=P.length := by
 induction P with
 | nil => simp [MafScheduler.badParents]
 | cons U P ih =>
  cases h : restrictionAgrees T S U <;> simp [MafScheduler.badParents,List.filter_cons,h] at ih ⊢ <;> omega

theorem actual_other_disjoint_bad (T S : Tree) (P : OrdinaryDispatch.Forest)
 (three : P.length=3) (notAll : P.all (restrictionAgrees T S)=false)
 (notTwo : (P.filter (restrictionAgrees T S)).length≠2) : 2≤MafScheduler.badParents T S P := by
 have balance := bad_good_balance T S P
 have notFull : (P.filter (restrictionAgrees T S)).length≠P.length := by
  intro eq
  have all := List.length_filter_eq_length_iff.1 eq
  have yes := List.all_eq_true.2 all
  simp [notAll] at yes
 omega
end OrdinaryDispatch.DisjointParents
