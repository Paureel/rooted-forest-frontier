import PaidGuardSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork

theorem vertex_nodup_rows (qs : List RMAF.Vertex) (N A : Nat)
 (addr : ∀q,q∈qs→q.length≤N) (count : qs.length≤A) :
 (vertexNodupMeter qs).work≤((2*N+2)*A+4)*(qs.length+1) := by
 induction qs with
 | nil=>simp [vertexNodupMeter]
 | cons q qs ih=>
  have c:=contains_address_work q qs N (addr q (by simp)) (fun v hv=>addr v (by simp [hv]))
  have scale:=Nat.mul_le_mul_left (2*N+2) (show qs.length≤A by simp only [List.length_cons] at count;omega)
  have r:=ih (fun v hv=>addr v (by simp [hv])) (by simp only [List.length_cons] at count;omega)
  rw [Nat.mul_succ] at r
  simp only [vertexNodupMeter,List.length_cons,Nat.mul_succ];omega

def guardBudget (N : Nat) :=((2*N+2)*N+4)*(N+1)+(4*(N+1)+7)*(N+1)+
 8*(N+1)^2+partitionCap N+120*(N+1)^5+arcPartitionBudget N N+32*(N+1)+3*N+18

theorem current_guard_work (T S : Tree) (c : Branch) (N : Nat)
 (tn : treeNodes (current T S c)≤N) (cuts : c.originalCuts.length≤N)
 (addr : ∀q,q∈c.originalCuts→q.length≤N)
 (pl : c.partition.length≤N) (flat : c.partition.flatten.length≤N) :
 (currentGuardMeter T S c).work≤guardBudget N := by
 have n:=vertex_nodup_rows c.originalCuts N N addr cuts
 have ncap:=Nat.mul_le_mul_left ((2*N+2)*N+4) (Nat.add_le_add_right cuts 1)
 have a:=meterAll_bound (fun q=>let s:=meterSubtree (current T S c) q;(⟨!q.isEmpty&&s.value.isSome,s.work+3⟩:Charged Bool)) c.originalCuts (4*(N+1)+3) (by
  intro q hq;have h:=meterSubtree_bound (current T S c) q
  have cap:=Nat.mul_le_mul_left 4 (Nat.add_le_add_right (addr q hq) 1)
  dsimp only;omega)
 have acap:=Nat.mul_le_mul_left (4*(N+1)+3+4) (Nat.add_le_add_right cuts 1)
 have l:=meterLeaves_cap (current T S c) N tn
 have ln:=Nat.le_trans (leaves_nodes (current T S c)) tn
 have p:=meterPartition_bound (leaves (current T S c)) c.partition N ln pl flat
 have blocks (B) (hb:B∈c.partition) : B.length≤N:=by
  exact Nat.le_trans (List.length_le_length_flatten hb) flat
 have e:=meterPairwise_polynomial (current T S c) c.partition N tn ln pl blocks
 have r:=arc_partition_work (current T S c) c.originalCuts N tn addr
 have rscale:=Nat.mul_le_mul_left (arcStepBudget N) (Nat.add_le_add_right cuts 1)
 have payload:=arc_partition_payload (current T S c) c.originalCuts
 have eq:=forest_eq_work c.partition (arcPartitionMeter (current T S c) c.originalCuts).value
 simp only [currentGuardMeter,meterLeaves_value,guardBudget,arcPartitionBudget] at *
 omega
end Universal233.Rule5ExecutionSource
