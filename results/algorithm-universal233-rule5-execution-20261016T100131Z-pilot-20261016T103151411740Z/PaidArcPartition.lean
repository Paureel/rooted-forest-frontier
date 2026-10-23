import PaidCurrentSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork BinaryExchange
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322

/-- Both literal filters are executed; the complement is not obtained free
from a shared classification pass. Empty-block filtering is also charged. -/
def splitBlockMeter (X B : List Nat) : Charged (List (List Nat)) :=
 let y:=meterFilter (fun x=>meterContains x X) B
 let n:=meterFilter (fun x=>let a:=meterContains x X;⟨!a.value,a.work+1⟩) B
 let f:=meterFilter (fun C:List Nat=>⟨!C.isEmpty,2⟩) [y.value,n.value]
 ⟨f.value,y.work+n.work+f.work+5⟩

@[simp] theorem split_block_value (X B : List Nat) :
 (splitBlockMeter X B).value=BinaryExchange.split B X.contains := by
 simp only [splitBlockMeter,meterFilter_value,meterContains_value,BinaryExchange.split,BinaryExchange.yes,BinaryExchange.no]

def splitForestMeter (X : List Nat) : List (List Nat)→Charged (List (List Nat))
 | []=>⟨[],1⟩
 | B::P=>let a:=splitBlockMeter X B;let r:=splitForestMeter X P
          ⟨a.value++r.value,a.work+r.work+a.value.length+3⟩

@[simp] theorem split_forest_value (X : List Nat) (P : List (List Nat)) :
 (splitForestMeter X P).value=splitForest P X := by
 induction P <;> simp_all [splitForestMeter,splitForest,BinaryExchange.splitAll]

theorem yes_no_length (q : Nat→Bool) (B : List Nat) :
 (BinaryExchange.yes B q).length+(BinaryExchange.no B q).length=B.length := by
 induction B with
 | nil=>rfl
 | cons x B ih=>cases h:q x <;> simp [BinaryExchange.yes,BinaryExchange.no,h] at * <;> omega

theorem split_block_flat (q : Nat→Bool) (B : List Nat) :
 (BinaryExchange.split B q).flatten.length=B.length := by
 have h:=yes_no_length q B
 by_cases hy:BinaryExchange.yes B q=[] <;> by_cases hn:BinaryExchange.no B q=[] <;>
  simp [BinaryExchange.split,hy,hn,List.isEmpty_iff] at * <;> omega

theorem split_forest_flat (X : List Nat) (P : List (List Nat)) :
 (splitForest P X).flatten.length=P.flatten.length := by
 induction P with
 | nil=>rfl
 | cons B P ih=>
  simpa only [splitForest,BinaryExchange.splitAll,List.flatMap_cons,List.flatten_append,List.flatten_cons,List.length_append,split_block_flat] using congrArg (B.length+·) ih

theorem nonempty_count (P : List (List Nat)) (ne : ∀B,B∈P→B≠[]) : P.length≤P.flatten.length := by
 induction P with
 | nil=>simp
 | cons B P ih=>
  have b:=List.length_pos_iff.2 (ne B (by simp))
  have tail:=ih (fun C hC=>ne C (by simp [hC]))
  simp only [List.length_cons,List.flatten_cons,List.length_append];omega

theorem split_forest_count (X : List Nat) (P : List (List Nat)) :
 (splitForest P X).length≤P.flatten.length := by
 rw [←split_forest_flat X P]
 exact nonempty_count _ (BinaryExchange.splitAll_nonempty P X.contains)

theorem split_block_work (X B : List Nat) (N : Nat) (xl : X.length≤N) (bl : B.length≤N) :
 (splitBlockMeter X B).work≤32*(N+1)^2 := by
 have point (x : Nat) : (meterContains x X).work≤4*(N+1):=by have h:=meterContains_bound x X;omega
 have y:=meterFilter_bound (fun x=>meterContains x X) B (4*(N+1)) (fun x _=>point x)
 have n:=meterFilter_bound (fun x=>let a:=meterContains x X;(⟨!a.value,a.work+1⟩:Charged Bool)) B (4*(N+1)+1) (fun x _=>by have h:=point x;dsimp only;omega)
 have f:=meterFilter_bound (fun C:List Nat=>(⟨!C.isEmpty,2⟩:Charged Bool))
  [(meterFilter (fun x=>meterContains x X) B).value,(meterFilter (fun x=>let a:=meterContains x X;(⟨!a.value,a.work+1⟩:Charged Bool)) B).value] 2 (by intros;simp)
 have yy:=Nat.mul_le_mul_left (4*(N+1)+4) (Nat.add_le_add_right bl 1)
 have nn:=Nat.mul_le_mul_left (4*(N+1)+1+4) (Nat.add_le_add_right bl 1)
 have pos:1≤(N+1)*(N+1):=by have h:=Nat.one_le_pow 2 (N+1) (by omega);simpa [Nat.pow_two] using h
 simp only [splitBlockMeter,List.length_cons,List.length_nil,Nat.pow_two,Nat.add_mul,Nat.mul_add,Nat.mul_one] at *
 omega

theorem split_forest_work (X : List Nat) (P : List (List Nat)) (N : Nat)
 (xl : X.length≤N) (pl : P.flatten.length≤N) :
 (splitForestMeter X P).work≤(32*(N+1)^2+5)*(P.length+1) := by
 induction P with
 | nil=>simp [splitForestMeter]
 | cons B P ih=>
  have bl:B.length≤N:=by simp only [List.flatten_cons,List.length_append] at pl;omega
  have tail:=ih (by simp only [List.flatten_cons,List.length_append] at pl;omega)
  have a:=split_block_work X B N xl bl
  have ac:(splitBlockMeter X B).value.length≤2:=by rw [split_block_value];exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  simp only [splitForestMeter,List.length_cons,Nat.mul_succ];omega

def arcFromMeter (T : Tree) : List RMAF.Vertex→List (List Nat)→Charged (List (List Nat))
 | [],P=>⟨P,1⟩
 | q::qs,P=>let x:=meterSubtreeLabels T q;let s:=splitForestMeter x.value P
             let r:=arcFromMeter T qs s.value
             ⟨r.value,x.work+s.work+r.work+3⟩

@[simp] theorem arc_from_value (T : Tree) (qs : List RMAF.Vertex) (P : List (List Nat)) :
 (arcFromMeter T qs P).value=arcPartitionFrom T qs P := by
 induction qs generalizing P <;> simp_all [arcFromMeter,arcPartitionFrom]

def arcPartitionMeter (T : Tree) (qs : List RMAF.Vertex) : Charged (List (List Nat)) :=
 let l:=meterLeaves T;let r:=arcFromMeter T qs [l.value];⟨r.value,l.work+r.work+3⟩

@[simp] theorem arc_partition_value (T : Tree) (qs : List RMAF.Vertex) :
 (arcPartitionMeter T qs).value=arcPartition T qs := by simp [arcPartitionMeter,arcPartition]
end Universal233.Rule5ExecutionSource
