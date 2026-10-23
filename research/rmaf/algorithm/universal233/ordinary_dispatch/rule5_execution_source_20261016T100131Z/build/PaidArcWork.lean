import PaidArcPartition
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork BinaryExchange
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322

theorem arc_from_flat (T : Tree) (qs : List RMAF.Vertex) (P : List (List Nat)) :
 (arcFromMeter T qs P).value.flatten.length=P.flatten.length := by
 induction qs generalizing P with
 | nil=>rfl
 | cons q qs ih=>simpa only [arcFromMeter,split_forest_value,split_forest_flat] using ih (splitForestMeter (meterSubtreeLabels T q).value P).value

theorem arc_from_count (T : Tree) (qs : List RMAF.Vertex) (P : List (List Nat)) (N : Nat)
 (flat : P.flatten.length≤N) (count : P.length≤N+1) :
 (arcFromMeter T qs P).value.length≤N+1 := by
 induction qs generalizing P with
 | nil=>exact count
 | cons q qs ih=>
  apply ih
  · simpa only [split_forest_value,split_forest_flat] using flat
  · have h:=split_forest_count (meterSubtreeLabels T q).value P
    rw [split_forest_value];omega

def arcStepBudget (N : Nat) :=16*(N+1)^2+(64*(N+1)^2+5)*(N+2)+4

theorem arc_from_work (T : Tree) (qs : List RMAF.Vertex) (P : List (List Nat)) (N : Nat)
 (tn : treeNodes T≤N) (addr : ∀q,q∈qs→q.length≤N)
 (flat : P.flatten.length≤N) (count : P.length≤N+1) :
 (arcFromMeter T qs P).work≤arcStepBudget N*(qs.length+1) := by
 induction qs generalizing P with
 | nil=>simp only [arcFromMeter,List.length_nil,Nat.zero_add,Nat.mul_one];unfold arcStepBudget;omega
 | cons q qs ih=>
  have ax:=meterSubtreeLabels_bound T q N tn (addr q (by simp))
  have xl:(meterSubtreeLabels T q).value.length≤N:=by rw [meterSubtreeLabels_value];exact Nat.le_trans (subtreeLabels_length T q) tn
  have sx:=split_forest_work (meterSubtreeLabels T q).value P N xl flat
  have scale:=Nat.mul_le_mul_left (64*(N+1)^2+5) (Nat.add_le_add_right count 1)
  simp only [Nat.add_assoc,Nat.reduceAdd] at scale
  have subflat:(splitForestMeter (meterSubtreeLabels T q).value P).value.flatten.length≤N:=by simpa only [split_forest_value,split_forest_flat] using flat
  have subcount:(splitForestMeter (meterSubtreeLabels T q).value P).value.length≤N+1:=by rw [split_forest_value];have h:=split_forest_count (meterSubtreeLabels T q).value P;omega
  have r:=ih _ (fun v hv=>addr v (by simp [hv])) subflat subcount
  simp only [arcFromMeter,List.length_cons,Nat.mul_succ]
  change _≤arcStepBudget N*qs.length+arcStepBudget N+arcStepBudget N
  rw [Nat.mul_succ] at r
  unfold arcStepBudget at *;omega

def arcPartitionBudget (N A : Nat) :=8*(N+1)^2+arcStepBudget N*(A+1)+3

theorem arc_partition_work (T : Tree) (qs : List RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (addr : ∀q,q∈qs→q.length≤N) :
 (arcPartitionMeter T qs).work≤arcPartitionBudget N qs.length := by
 have l:=meterLeaves_cap T N tn
 have ln:=Nat.le_trans (leaves_nodes T) tn
 have r:=arc_from_work T qs [(meterLeaves T).value] N tn addr
  (by simpa using ln) (by simp)
 simp only [arcPartitionMeter,arcPartitionBudget];omega

theorem arc_partition_payload (T : Tree) (qs : List RMAF.Vertex) :
 (arcPartitionMeter T qs).value.flatten.length=(leaves T).length ∧
 (arcPartitionMeter T qs).value.length≤(leaves T).length+1 := by
 have f:=arc_from_flat T qs [(meterLeaves T).value]
 have c:=arc_from_count T qs [(meterLeaves T).value] (leaves T).length (by simp) (by simp)
 simpa only [arcPartitionMeter,meterLeaves_value,List.flatten_cons,List.flatten_nil,List.append_nil] using And.intro f c
end Universal233.Rule5ExecutionSource
