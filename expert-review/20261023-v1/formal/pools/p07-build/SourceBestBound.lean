import SourceBestMeter
namespace OrdinaryDispatch.Hard2SourceWork
open RMAF Universal233 WholeSourceWork CoreWork

/-- A selected tail is an actual tail occurrence; both score calls are paid. -/
theorem sourceBestMeter_bound {α : Type} (cost : α→Charged Nat) (valid : α→Charged Bool)
 (xs : List α) (C K : Nat)
 (score:∀x,x∈xs→(cost x).work≤C) (check:∀x,x∈xs→(valid x).work≤K) :
 (sourceBestMeter cost valid xs).work≤(K+2*C+12)*xs.length+2:=by
 induction xs with
 | nil=>simp [sourceBestMeter]
 | cons x xs ih=>
   have hx:=check x (by simp)
   have cx:=score x (by simp)
   have tail:=ih (by intro y hm;exact score y (by simp [hm]))
    (by intro y hm;exact check y (by simp [hm]))
   simp only [sourceBestMeter]
   split
   · cases ht:(sourceBestMeter cost valid xs).value with
     | none=>simp only [Charged.work,List.length_cons,Nat.mul_add,Nat.mul_one];omega
     | some y=>
       have eq:best (fun z=>(cost z).value) (fun z=>(valid z).value) xs=some y:=by
        simpa only [sourceBestMeter_value] using ht
       have mem:=(best_spec _ _ xs y eq).1
       have cy:=score y (by simp [mem])
       simp only [Charged.work,List.length_cons,Nat.mul_add,Nat.mul_one];omega
   · simp only [Charged.work,List.length_cons,Nat.mul_add,Nat.mul_one];omega
end OrdinaryDispatch.Hard2SourceWork
