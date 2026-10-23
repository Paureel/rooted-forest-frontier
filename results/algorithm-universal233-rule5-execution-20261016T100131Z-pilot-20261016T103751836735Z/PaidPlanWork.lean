import PaidRequestsSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent VertexGeometry Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork Rule5SelectedLocalWork Case322Extraction Case322PaidGuard Rule5PaidSelector

def sideAtBudget (N : Nat) :=32*(N+1)^2+12*N+13

theorem side_at_work (T : Tree) (b c : Nat) (q : RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (addr : q.length≤N) : (sideAtMeter T b c q).work≤sideAtBudget N := by
 have d:=drop_last_work q
 have dl:q.dropLast.length≤N:=by simp only [List.length_dropLast];omega
 have x:=meterSubtreeLabels_bound T q.dropLast N tn dl
 have xl:=Nat.le_trans (subtreeLabels_length T q.dropLast) tn
 have bx:=meterContains_bound b (DepthOne.subtreeLabels T q.dropLast)
 have cy:=meterContains_bound c (DepthOne.subtreeLabels T q.dropLast)
 simp only [sideAtMeter,drop_last_value,meterSubtreeLabels_value,sideAtBudget];omega

def sideEdgesBudget (T : Tree) (N : Nat) :=cutsBudget (leaves T).length+(sideAtBudget N+4)*(2*(leaves T).length+1)+2

theorem side_edges_work (T : Tree) (b c : Nat) (N : Nat) (tn : treeNodes T≤N) :
 (sideEdgesMeter T b c).work≤sideEdgesBudget T N ∧ (cSideMeter T b c).work≤sideEdgesBudget T N := by
 have k:=cuts_work T b c;have count:=cuts_count T b c
 have l:=Nat.le_trans (leaves_nodes T) tn
 have addr (q) (hq:q∈(cutsMeter T b c).value) : q.length≤N:=by have h:=cuts_address T b c hq;omega
 have f:=meterFilter_bound (sideAtMeter T b c) (cutsMeter T b c).value (sideAtBudget N) (fun q hq=>side_at_work T b c q N tn (addr q hq))
 have g:=meterFilter_bound (sideAtMeter T c b) (cutsMeter T b c).value (sideAtBudget N) (fun q hq=>side_at_work T c b q N tn (addr q hq))
 have scale:=Nat.mul_le_mul_left (sideAtBudget N+4) (Nat.add_le_add_right count 1)
 simp only [sideEdgesMeter,cSideMeter,sideEdgesBudget];constructor <;> omega

theorem side_edges_domain (T : Tree) (b c : Nat) :
 (sideEdgesMeter T b c).value.length≤2*(leaves T).length ∧
 (cSideMeter T b c).value.length≤2*(leaves T).length ∧
 (∀q,q∈(sideEdgesMeter T b c).value→q.length+1≤(leaves T).length) ∧
 (∀q,q∈(cSideMeter T b c).value→q.length+1≤(leaves T).length) := by
 have k:=cuts_count T b c
 have f:=List.length_filter_le (fun q=>(sideAtMeter T b c q).value) (cutsMeter T b c).value
 have g:=List.length_filter_le (fun q=>(sideAtMeter T c b q).value) (cutsMeter T b c).value
 simp only [sideEdgesMeter,cSideMeter,meterFilter_value]
 exact ⟨by omega,by omega,fun q hq=>cuts_address T b c (List.mem_filter.1 hq).1,fun q hq=>cuts_address T b c (List.mem_filter.1 hq).1⟩

def withoutABudget (T : Tree) (N : Nat) :=sideEdgesBudget T N+(16*(N+1)^2+4*(N+1)+5)*(2*(leaves T).length+1)+2

theorem without_a_work (T : Tree) (a b c N : Nat) (tn : treeNodes T≤N) :
 (withoutAMeter T a b c).work≤withoutABudget T N := by
 have s:=(side_edges_work T b c N tn).1
 have dom:=side_edges_domain T b c
 have l:=Nat.le_trans (leaves_nodes T) tn
 have f:=meterFilter_bound (fun q=>let x:=meterSubtreeLabels T q;let z:=meterContains a x.value;(⟨!z.value,x.work+z.work+1⟩:Charged Bool)) (sideEdgesMeter T b c).value (16*(N+1)^2+4*(N+1)+1) (by
  intro q hq
  have addr:q.length≤N:=by have h:=dom.2.2.1 q hq;omega
  have x:=meterSubtreeLabels_bound T q N tn addr
  have xl:=Nat.le_trans (subtreeLabels_length T q) tn
  have z:=meterContains_bound a (DepthOne.subtreeLabels T q)
  dsimp only;rw [meterSubtreeLabels_value];omega)
 have scale:=Nat.mul_le_mul_left (16*(N+1)^2+4*(N+1)+1+4) (Nat.add_le_add_right dom.1 1)
 simp only [Nat.add_assoc,Nat.reduceAdd] at f scale
 simp only [withoutAMeter,withoutABudget];omega

theorem without_a_domain (T : Tree) (a b c : Nat) :
 (withoutAMeter T a b c).value.length≤2*(leaves T).length ∧
 ∀q,q∈(withoutAMeter T a b c).value→q.length+1≤(leaves T).length := by
 have d:=side_edges_domain T b c
 have f:=List.length_filter_le (fun q=>!(subtreeLabels T q).contains a) (sideEdgesMeter T b c).value
 rw [←b_side_value] at f
 constructor
 · simpa only [without_a_value,bSideWithoutA,←b_side_value] using Nat.le_trans f d.1
 · intro q hq;rw [without_a_value] at hq
   exact d.2.2.1 q (by simpa only [b_side_value] using (List.mem_filter.1 hq).1)

theorem raw_plan_count (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) :
 (rawPlanMeter T S a b c qa qb ub uc).value.length≤4 := by
 simp only [rawPlanMeter]
 split
 · rfl
 · split <;> simp [typeIIMeter]
end Universal233.Rule5ExecutionSource
