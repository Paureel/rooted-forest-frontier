import PaidPlanPolynomial
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork Rule5SelectedLocalWork Case322Extraction Case322PaidGuard Rule5PaidSelector

theorem current_tree_caps {T S : Tree} (D : LiteralGeometry T S) (c : Branch) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 treeNodes (current T S c)≤N ∧ (leaves (current T S c)).Nodup := by
 by_cases role:c.role=.source <;> simp only [current,role,ite_true,ite_false] <;> first | exact ⟨sn,D.properS⟩ | exact ⟨tn,D.properT⟩

theorem guarded_branch_caps {T S : Tree} (D : LiteralGeometry T S) (c : Branch) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (guard : currentGuard T S c=true) :
 c.originalCuts.length≤N ∧ (∀q,q∈c.originalCuts→q.length≤N) ∧
 c.partition.length≤N ∧ c.partition.flatten.length≤N := by
 have caps:=current_tree_caps D c N tn sn
 have ln:=Nat.le_trans (leaves_nodes (current T S c)) caps.1
 have full : c.originalCuts.Nodup ∧
   c.originalCuts.all (fun q=>!q.isEmpty&&(subtree (current T S c) q).isSome)=true ∧
   partitionCheck (leaves (current T S c)) c.partition=true ∧
   pairwiseEmbeddings (current T S c) c.partition=true ∧ c.partition.length=paid c+1 ∧
   c.partition=arcPartition (current T S c) c.originalCuts:=by
  simpa only [currentGuard,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,and_assoc] using guard
 have pl:=SourceCoverage.partitionCheck_block_bound _ _ full.2.2.1
 have fl:=(FinalCutRecovery.checked_flatten_perm _ _ caps.2 full.2.2.1).length_eq
 have cost:=full.2.2.2.2.1
 unfold paid at cost
 refine ⟨by omega,?_,by omega,by omega⟩
 intro q hq
 have valid:= (List.all_eq_true.1 full.2.1) q hq
 have parts : !q.isEmpty=true ∧ (subtree (current T S c) q).isSome=true:=by simpa only [Bool.and_eq_true] using valid
 have sub : (subtree (current T S c) q).isSome=true:=parts.2
 obtain ⟨U,hU⟩:=Option.isSome_iff_exists.1 sub
 have depth:=subtree_depth hU;omega

def guardedPlanBudget (T S : Tree) (N : Nat) :=literalPlanBudget T S N+5*(guardBudget N+4)+2

theorem guarded_literal_work {T S : Tree} (D : LiteralGeometry T S) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (guardedPlanMeter D (literalPlanMeter D)).work≤guardedPlanBudget T S N := by
 have p:=literal_plan_work D N tn sn
 have count:=raw_plan_count T S D.a D.b D.c D.qa (bArc D.w D.sb) D.ub D.uc
 have f:=meterFilter_bound (currentGuardMeter T S) (literalPlanMeter D).value (guardBudget N) (by
  intro c hc
  have mem:c∈literalPlan D:=by simpa only [literal_plan_value] using hc
  have guard:=literalPlan_guards D c mem
  have caps:=guarded_branch_caps D c N tn sn guard
  exact current_guard_work T S c N (current_tree_caps D c N tn sn).1 caps.1 caps.2.1 caps.2.2.1 caps.2.2.2)
 have pc:(literalPlanMeter D).value.length≤4:=count
 have scale:=Nat.mul_le_mul_left (guardBudget N+4) (Nat.add_le_add_right pc 1)
 simp only [guardedPlanMeter,guardedPlanBudget];omega

def requestBudget (N : Nat) :=(4*(N+2)*N+3)*N+2*N+8

theorem request_for_work {T S : Tree} (D : LiteralGeometry T S) (q : Nat) (c : Branch) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) (guard : currentGuard T S c=true) :
 (requestForMeter T S q c).work≤requestBudget N := by
 have caps:=guarded_branch_caps D c N tn sn guard
 have aux (P : List (List Nat)) (B : List Nat) (hb:B∈P) : B.length≤P.flatten.length:=by
  induction P with
  | nil=>simp at hb
  | cons C P ih=>simp only [List.mem_cons] at hb;simp only [List.flatten_cons,List.length_append];rcases hb with rfl|hb;omega;have h:=ih hb;omega
 have s:=source_forest_work (current T S c) c.partition N (fun B hb=>Nat.le_trans (aux _ B hb) caps.2.2.2)
 have node:=(current_tree_caps D c N tn sn).1
 have scale:=Nat.mul_le_mul_left (4*(N+2)) node
 have rows:=Nat.mul_le_mul (Nat.add_le_add_right scale 3) caps.2.2.1
 simp only [requestForMeter];split <;> dsimp only <;> unfold requestBudget <;> omega

theorem request_list_rows (T S : Tree) (q : Nat) (cs : List Branch) (A : Nat)
 (point : ∀c,c∈cs→(requestForMeter T S q c).work≤A) :
 (requestListMeter T S q cs).work≤(A+3)*cs.length+1 := by
 induction cs with
 | nil=>simp [requestListMeter]
 | cons c cs ih=>
  have h:=point c (by simp);have r:=ih (fun d hd=>point d (by simp [hd]))
  simp only [requestListMeter,List.length_cons,Nat.mul_succ];omega

def requestsBudget (T S : Tree) (N : Nat) :=guardedPlanBudget T S N+4*(requestBudget N+3)+3

theorem requests_work {T S : Tree} (D : LiteralGeometry T S) (q N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) : (requestsMeter D q).work≤requestsBudget T S N := by
 have g:=guarded_literal_work D N tn sn
 have cnt:(guardedPlanMeter D (literalPlanMeter D)).value.length≤4:=by
  rw [guarded_plan_value D _ (literal_plan_value D),guardedPlan_eq,literalPlan,←raw_plan_value]
  exact raw_plan_count _ _ _ _ _ _ _ _ _
 have r:=request_list_rows T S q (guardedPlanMeter D (literalPlanMeter D)).value (requestBudget N) (by
  intro c hc
  have mem:c∈guardedPlan D:=by rw [←guarded_plan_value D _ (literal_plan_value D)];exact hc
  exact request_for_work D q c N tn sn (List.mem_filter.1 mem).2)
 have scale:=Nat.mul_le_mul_left (requestBudget N+3) cnt
 simp only [requestsMeter,requestsBudget];omega

theorem requests_count {T S : Tree} (D : LiteralGeometry T S) (q : Nat) : (requestsMeter D q).value.length≤4 := by
 rw [requests_value]
 have filter:=List.length_filterMap_le (requestFor T S q) (guardedPlan D)
 have plan: (guardedPlan D).length≤4:=by rw [guardedPlan_eq,literalPlan,←raw_plan_value];exact raw_plan_count _ _ _ _ _ _ _ _ _
 exact Nat.le_trans filter plan
end Universal233.Rule5ExecutionSource
