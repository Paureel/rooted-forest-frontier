import PaidAnswerLedger
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent VertexGeometry Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork Rule5SelectedLocalWork Case322Extraction Case322PaidGuard Rule5PaidSelector

def hardBranchBudget (S : Tree) :=cutsBudget (leaves S).length+partitionBudget (leaves S).length+4
def bBranchBudget (S : Tree) :=singletonPartitionBudget (leaves S).length+4

theorem hard_branch_work (S : Tree) (a b : Nat) : (hardBranchMeter S a b).work≤hardBranchBudget S := by
 have k:=cuts_work S a b;have p:=partition_work S a b;simp only [hardBranchMeter,hardBranchBudget];omega
theorem b_branch_work (S : Tree) (b : Nat) (qb : RMAF.Vertex) : (bBranchMeter S b qb).work≤bBranchBudget S := by
 have p:=singleton_partition_work S b;simp only [bBranchMeter,bBranchBudget];omega

def targetBranchBudget (N : Nat) :=arcPartitionBudget N (2*N+1)+3

theorem target_branch_work (T : Tree) (qs : List RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (addr : ∀q,q∈qs→q.length≤N) (count : qs.length≤2*N+1) :
 (targetBranchMeter T qs).work≤targetBranchBudget N := by
 have p:=arc_partition_work T qs N tn addr
 have scale:=Nat.mul_le_mul_left (arcStepBudget N) (Nat.add_le_add_right count 1)
 simp only [targetBranchMeter,targetBranchBudget,arcPartitionBudget] at *;omega

def typeBudget (S : Tree) (N : Nat) :=hardBranchBudget S+bBranchBudget S+2*targetBranchBudget N+5

theorem type_i_work (T S : Tree) (a b : Nat) (qa qb u v : RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (aq : qa.length≤N) (au : u.length≤N) (av : v.length≤N) :
 (typeIMeter T S a b qa qb u v).work≤typeBudget S N := by
 have k:=hard_branch_work S a b;have p:=b_branch_work S b qb
 have l:=target_branch_work T [qa,u] N tn (by intro q hq;simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;rcases hq with rfl|rfl <;> assumption) (by simp only [List.length_cons,List.length_nil];have h:=treeNodes_pos T;omega)
 have r:=target_branch_work T [qa,v] N tn (by intro q hq;simp only [List.mem_cons,List.not_mem_nil,or_false] at hq;rcases hq with rfl|rfl <;> assumption) (by simp only [List.length_cons,List.length_nil];have h:=treeNodes_pos T;omega)
 simp only [typeIMeter,typeBudget];omega

theorem type_ii_work (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (aq : qa.length≤N) (addr : ∀q,q∈qs→q.length≤N) (count : qs.length≤2*N) :
 (typeIIMeter T S a b qa qb qs).work≤typeBudget S N := by
 have k:=hard_branch_work S a b;have p:=b_branch_work S b qb
 have l:=target_branch_work T (qa::qs) N tn (by intro q hq;rcases List.mem_cons.1 hq with rfl|hq;exact aq;exact addr q hq) (by simpa using Nat.add_le_add_right count 1)
 simp only [typeIIMeter,typeBudget];omega

def rawPlanBudget (T S : Tree) (N : Nat) :=sideEdgesBudget T N+withoutABudget T N+3*N+typeBudget S N+7

theorem raw_plan_work (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) (N : Nat)
 (tn : treeNodes T≤N) (aq : qa.length≤N) (ab : ub.length≤N) :
 (rawPlanMeter T S a b c qa qb ub uc).work≤rawPlanBudget T S N := by
 have e:=(side_edges_work T b c N tn).2
 have ed:=side_edges_domain T b c
 have w:=without_a_work T a b c N tn
 have wd:=without_a_domain T a b c
 have l:=lca_work ub uc
 have ln:=Nat.le_trans (leaves_nodes T) tn
 have lc:(lca ub uc).length≤N:=Nat.le_trans (lca_prefixes ub uc).1.length_le ab
 simp only [rawPlanMeter]
 split
 · rename_i u v tail he
   have um:u∈(cSideMeter T b c).value:=by rw [he];simp
   have vm:v∈(cSideMeter T b c).value:=by rw [he];simp
   have au:u.length≤N:=by have h:=ed.2.2.2 u um;omega
   have av:v.length≤N:=by have h:=ed.2.2.2 v vm;omega
   have p:=type_i_work T S a b qa qb u v N tn aq au av
   dsimp only;unfold rawPlanBudget;omega
 · split
   · have p:=type_ii_work T S a b qa qb [(lcaMeter ub uc).value] N tn aq (by intro q hq;rcases List.mem_singleton.1 hq with rfl;simpa using lc) (by simp only [List.length_cons,List.length_nil];have h:=treeNodes_pos T;omega)
     dsimp only;unfold rawPlanBudget;omega
   · have p:=type_ii_work T S a b qa qb (withoutAMeter T a b c).value N tn aq
       (fun q hq=>by have h:=wd.2 q hq;omega) (by omega)
     dsimp only;unfold rawPlanBudget;omega

def literalPlanBudget (T S : Tree) (N : Nat) :=rawPlanBudget T S N+N+2

theorem literal_plan_work {T S : Tree} (D : LiteralGeometry T S) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (literalPlanMeter D).work≤literalPlanBudget T S N := by
 have tl:=Nat.le_trans (leaves_nodes T) tn
 have sl:=Nat.le_trans (leaves_nodes S) sn
 have aq:D.qa.length≤N:=by have h:=subtree_depth D.leafA.valid.choose_spec;omega
 have ab:D.ub.length≤N:=by have h:=subtree_depth D.leafB.valid.choose_spec;omega
 have aw:D.w.length≤N:=by have h:=subtree_depth D.source;omega
 have p:=raw_plan_work T S D.a D.b D.c D.qa (bArc D.w D.sb) D.ub D.uc N tn aq ab
 simp only [literalPlanMeter,literalPlanBudget];omega
end Universal233.Rule5ExecutionSource
