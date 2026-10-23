import NumericReach
import ExtendedSourceInterface
namespace OrdinaryDispatch.GoodPairGlobalAssembly
open RMAF ForestState Universal233
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.GlobalNumeric

/-- The sealed weighted reservoir, with a local bill proved only at the actual
reachable source states. Every list occurrence remains in the Nat sum. -/
theorem sourceSubtotal_reach_weighted_aux (localDebit : OrdinaryWork) (q0 : Nat) (T0 S0 : Tree) (C : Rat)
 (localBound : ∀d T S r,Reach FastOrdinary.solve q0 T0 S0 d T S r→
  (localDebit T S r:Rat)≤C*Rule5ActualTrace.base^r) (q n : Nat) : ∀d (T S : Tree),
 (leaves T).length=n→DepthOne.proper T S=true→Reach FastOrdinary.solve q0 T0 S0 d T S q→
 (sourceSubtotal localDebit q T S:Rat)≤C*budgetTreeWork q T S := by
 induction q using Nat.strongRecOn generalizing n with
 | ind q qih=>
  induction n using Nat.strongRecOn with
  | ind n nih=>
   intro d T S hn hp path
   let xs:=(ordinaryStepTrace FastOrdinary.solve q T S).queries
   have point (pb : Query) (mem : pb∈xs) :
    (sourceSubtotal localDebit pb.2 pb.1.1 pb.1.2:Rat)≤C*budgetTreeWork pb.2 pb.1.1 pb.1.2:=by
    have b:=ordinaryStepTrace_bounds FastOrdinary.solve q hp pb.1 pb.2 mem
    have child : Reach FastOrdinary.solve q0 T0 S0 (d+1) pb.1.1 pb.1.2 pb.2:=Reach.next path mem
    by_cases eq:pb.2=q
    · have less:(leaves pb.1.1).length<n:=by have h:=b.2.2.2.2 eq;omega
      simpa only [eq] using nih (leaves pb.1.1).length less (d+1) pb.1.1 pb.1.2 rfl b.2.1 (by simpa only [eq] using child)
    · exact qih pb.2 (by omega) (leaves pb.1.1).length (d+1) pb.1.1 pb.1.2 rfl b.2.1 child
   have sum:=GenericForest.rat_sum_map_le xs
    (fun pb=>(sourceSubtotal localDebit pb.2 pb.1.1 pb.1.2:Rat))
    (fun pb=>C*budgetTreeWork pb.2 pb.1.1 pb.1.2) point
   rw [GenericForest.rat_sum_mul] at sum
   rw [sourceSubtotal_eq,Rat.natCast_add,queryWork_cast,budgetTreeWork_eq,Rat.mul_add]
   exact Rat.le_trans (Rat.add_le_add_right.mpr (localBound d T S q path))
    (Rat.add_le_add_left.mpr sum)

theorem sourceSubtotal_reach_bound (localDebit : OrdinaryWork) (q0 : Nat) (T0 S0 : Tree) (C : Rat)
 (positive : 0≤C) (localBound : ∀d T S r,Reach FastOrdinary.solve q0 T0 S0 d T S r→
  (localDebit T S r:Rat)≤C*Rule5ActualTrace.base^r)
 {d T S q} (hp : DepthOne.proper T S=true) (path : Reach FastOrdinary.solve q0 T0 S0 d T S q) :
 (sourceSubtotal localDebit q T S:Rat)≤C*callNodeFactor*((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 have sum:=sourceSubtotal_reach_weighted_aux localDebit q0 T0 S0 C localBound q (leaves T).length d T S rfl hp path
 have scale:=Rat.mul_le_mul_of_nonneg_left (budgetTreeWork_bound q T S hp) positive
 exact Rat.le_trans sum (by simpa only [Rat.mul_assoc] using scale)
end OrdinaryDispatch.GoodPairGlobalAssembly
