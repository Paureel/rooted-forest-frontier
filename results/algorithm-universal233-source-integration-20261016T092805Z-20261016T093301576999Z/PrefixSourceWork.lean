import GeneralAgreementWork
import WeightedOrdinaryWork
namespace OrdinaryDispatch.FullSourceWork
open RMAF ForestState Universal233 WholeSourceWork CoreWork
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open OrdinaryDispatch.EarlyLocalWork

def prefixCoefficient (N : Nat) : Nat := 2097152*(2*N+1)^6

/-- Actual sealed prefix source work at every invocation of the literal
ordinary tree. Branch builders, recursive forest overhead and reconstruction
are deliberately absent from this named subtotal. -/
def prefixTreeWork (q : Nat) (T S : Tree) : Nat :=
 (meterFront q T S).work+
 (((ordinaryStepTrace FastOrdinary.solve q T S).queries.attach).map fun pb=>
  prefixTreeWork pb.val.2 pb.val.1.1 pb.val.1.2).sum
termination_by (q,(leaves T).length)
decreasing_by exact ordinaryStepTrace_lex FastOrdinary.solve q T S _ _ pb.property

theorem prefixTreeWork_eq (q : Nat) (T S : Tree) :
 prefixTreeWork q T S=(meterFront q T S).work+
 queryWork (fun t s r=>prefixTreeWork r t s) (ordinaryStepTrace FastOrdinary.solve q T S).queries := by
 rw [prefixTreeWork.eq_def]
 unfold queryWork
 exact congrArg (fun L : List Nat=>(meterFront q T S).work+L.sum)
  (List.attach_map_val (l:=(ordinaryStepTrace FastOrdinary.solve q T S).queries)
   (f:=fun pb : Query=>prefixTreeWork pb.2 pb.1.1 pb.1.2))

theorem nat_query_scale (W V : OrdinaryWork) (xs : List Query) (K : Nat)
 (point : ∀pb,pb∈xs→W pb.1.1 pb.1.2 pb.2≤K*V pb.1.1 pb.1.2 pb.2) :
 queryWork W xs≤K*queryWork V xs := by
 induction xs with
 | nil=>simp [queryWork]
 | cons pb xs ih=>
  have a:=point pb (by simp)
  have b:=ih (fun p hp=>point p (by simp [hp]))
  simp only [queryWork,List.map_cons,List.sum_cons,Nat.mul_add] at b ⊢
  exact Nat.add_le_add a b

theorem prefix_local_cap (q : Nat) (T S : Tree) (N : Nat)
 (hp : DepthOne.proper T S=true) (size : (leaves T).length≤N) :
 (meterFront q T S).work≤prefixCoefficient N := by
 have same:=((DepthOne.proper_iff T S).1 hp).2.2.length_eq
 have t:=treeNodes_leafCount T;have s:=treeNodes_leafCount S
 exact meterFront_bound T S q (2*N) (by omega) (by omega)

theorem prefixTreeWork_count_aux (q n N : Nat) : ∀T S : Tree,
 (leaves T).length=n→n≤N→DepthOne.proper T S=true→
 prefixTreeWork q T S≤prefixCoefficient N*ordinaryCallNodes q T S := by
 induction q using Nat.strongRecOn generalizing n with
 | ind q qih=>
  induction n using Nat.strongRecOn with
  | ind n nih=>
   intro T S hn size hp
   let xs:=(ordinaryStepTrace FastOrdinary.solve q T S).queries
   have point (pb : Query) (mem : pb∈xs) :
    prefixTreeWork pb.2 pb.1.1 pb.1.2≤prefixCoefficient N*ordinaryCallNodes pb.2 pb.1.1 pb.1.2:=by
    have b:=ordinaryStepTrace_bounds FastOrdinary.solve q hp pb.1 pb.2 mem
    have childsize:(leaves pb.1.1).length≤N:=by omega
    by_cases eq:pb.2=q
    · have less:(leaves pb.1.1).length<n:=by have h:=b.2.2.2.2 eq;omega
      simpa only [eq] using nih (leaves pb.1.1).length less pb.1.1 pb.1.2 rfl childsize b.2.1
    · exact qih pb.2 (by omega) (leaves pb.1.1).length pb.1.1 pb.1.2 rfl childsize b.2.1
   have sum:=nat_query_scale (fun t s r=>prefixTreeWork r t s)
    (fun t s r=>ordinaryCallNodes r t s) xs (prefixCoefficient N) point
   have bill:=prefix_local_cap q T S N hp (by omega)
   rw [prefixTreeWork_eq,ordinaryCallNodes_eq,Nat.mul_add,Nat.mul_one]
   exact Nat.add_le_add bill sum

/-- Polynomial total for the actual prefix subtotal, at arbitrary current q.
No q<=current leaf count hypothesis or whole-local cost record is used. -/
theorem prefixTreeWork_bound (q : Nat) (T S : Tree) (hp : DepthOne.proper T S=true) :
 (prefixTreeWork q T S:Rat)≤(prefixCoefficient (leaves T).length:Rat)*callNodeFactor*
  ((leaves T).length+1:Nat)*Rule5ActualTrace.base^q := by
 have h:=prefixTreeWork_count_aux q (leaves T).length (leaves T).length T S rfl (Nat.le_refl _) hp
 have cast:=Rat.natCast_le_natCast.2 h
 rw [Rat.natCast_mul] at cast
 have scaled:=Rat.mul_le_mul_of_nonneg_left (ordinaryCallNodes_bound q T S hp)
  (Rat.natCast_nonneg (a:=prefixCoefficient (leaves T).length))
 exact Rat.le_trans cast (by simpa only [Rat.mul_assoc] using scaled)

structure PrefixReceipt where
 value : Option (List (List Nat))
 sourcePrefixWork : Nat

def prefixTreeMeter (q : Nat) (T S : Tree) : PrefixReceipt :=
 ⟨(ordinaryStepTrace FastOrdinary.solve q T S).value,prefixTreeWork q T S⟩

theorem prefixTreeMeter_value (q : Nat) (T S : Tree) :
 (prefixTreeMeter q T S).value=FastOrdinary.solve q T S := ordinaryStepTrace_value q T S
end OrdinaryDispatch.FullSourceWork
