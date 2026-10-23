import PaidGuardWork
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork Rule5SelectedLocalWork Case322Extraction Case322PaidGuard

/-- Source-side and target-side extraction each repeat the cut builder and
both parent-subtree materializations used by the literal predicates. -/
def sideAtMeter (T : Tree) (b c : Nat) (q : RMAF.Vertex) : Charged Bool :=
 let d:=dropLastMeter q;let x:=meterSubtreeLabels T d.value;let bx:=meterContains b x.value
 let e:=dropLastMeter q;let y:=meterSubtreeLabels T e.value;let cy:=meterContains c y.value
 ⟨bx.value && !cy.value,d.work+x.work+bx.work+e.work+y.work+cy.work+3⟩
@[simp] theorem side_at_value (T : Tree) (b c : Nat) (q : RMAF.Vertex) :
 (sideAtMeter T b c q).value=(subtreeLabels T q.dropLast).contains b && !(subtreeLabels T q.dropLast).contains c := by
 simp only [sideAtMeter,drop_last_value,meterSubtreeLabels_value,meterContains_value,hpLabels_eq]

def sideEdgesMeter (T : Tree) (b c : Nat) : Charged (List RMAF.Vertex) :=
 let k:=cutsMeter T b c;let f:=meterFilter (sideAtMeter T b c) k.value
 ⟨f.value,k.work+f.work+2⟩
@[simp] theorem b_side_value (T : Tree) (b c : Nat) : (sideEdgesMeter T b c).value=bSideEdges T b c := by
 simp only [sideEdgesMeter,meterFilter_value,side_at_value,cuts_value,bSideEdges]
/-- The c-side keeps the original ordered b,c cut invocation. -/
def cSideMeter (T : Tree) (b c : Nat) : Charged (List RMAF.Vertex) :=
 let k:=cutsMeter T b c;let f:=meterFilter (sideAtMeter T c b) k.value
 ⟨f.value,k.work+f.work+2⟩
@[simp] theorem c_side_meter_value (T : Tree) (b c : Nat) : (cSideMeter T b c).value=cSideEdges T b c := by
 simp only [cSideMeter,meterFilter_value,side_at_value,cuts_value,cSideEdges]

def withoutAMeter (T : Tree) (a b c : Nat) : Charged (List RMAF.Vertex) :=
 let s:=sideEdgesMeter T b c
 let f:=meterFilter (fun q=>let x:=meterSubtreeLabels T q;let z:=meterContains a x.value;⟨!z.value,x.work+z.work+1⟩) s.value
 ⟨f.value,s.work+f.work+2⟩
@[simp] theorem without_a_value (T : Tree) (a b c : Nat) : (withoutAMeter T a b c).value=bSideWithoutA T a b c := by
 simp only [withoutAMeter,meterFilter_value,meterSubtreeLabels_value,meterContains_value,b_side_value,bSideWithoutA,hpLabels_eq]

def lcaMeter : RMAF.Vertex→RMAF.Vertex→Charged RMAF.Vertex
 | [],_=>⟨[],1⟩ | _::_,[]=>⟨[],1⟩
 | x::xs,y::ys=>if x=y then let r:=lcaMeter xs ys;⟨x::r.value,r.work+3⟩ else ⟨[],2⟩
@[simp] theorem lca_value (p q : RMAF.Vertex) : (lcaMeter p q).value=lca p q := by
 induction p generalizing q <;> cases q <;> simp_all [lcaMeter,lca]
theorem lca_work (p q : RMAF.Vertex) : (lcaMeter p q).work≤3*p.length+1 := by
 induction p generalizing q with
 | nil=>simp [lcaMeter]
 | cons x xs ih=>cases q with
  | nil=>simp [lcaMeter]
  | cons y ys=>have r:=ih ys;simp only [lcaMeter];split <;> dsimp only <;> simp only [List.length_cons] <;> omega

def hardBranchMeter (S : Tree) (a b : Nat) : Charged Branch :=
 let k:=cutsMeter S a b;let p:=partitionMeter S a b
 ⟨⟨.source,k.value,p.value⟩,k.work+p.work+4⟩
def bBranchMeter (S : Tree) (b : Nat) (qb : RMAF.Vertex) : Charged Branch :=
 let p:=singletonPartitionMeter S b;⟨⟨.source,[qb],p.value⟩,p.work+4⟩
def targetBranchMeter (T : Tree) (qs : List RMAF.Vertex) : Charged Branch :=
 let p:=arcPartitionMeter T qs;⟨⟨.target,qs,p.value⟩,p.work+3⟩
@[simp] theorem hard_branch_value (S : Tree) (a b : Nat) : (hardBranchMeter S a b).value=hardBranch S a b:=by simp [hardBranchMeter,hardBranch,partition_value]
@[simp] theorem b_branch_value (S : Tree) (b : Nat) (qb : RMAF.Vertex) : (bBranchMeter S b qb).value=bBranch S b qb:=by simp [bBranchMeter,bBranch,singleton_partition_value]
@[simp] theorem target_branch_value (T : Tree) (qs : List RMAF.Vertex) : (targetBranchMeter T qs).value=targetBranch T qs:=by simp [targetBranchMeter,targetBranch]

def typeIMeter (T S : Tree) (a b : Nat) (qa qb q r : RMAF.Vertex) : Charged (List Branch) :=
 let h:=hardBranchMeter S a b;let s:=bBranchMeter S b qb
 let l:=targetBranchMeter T [qa,q];let u:=targetBranchMeter T [qa,r]
 ⟨[h.value,s.value,l.value,u.value],h.work+s.work+l.work+u.work+5⟩
def typeIIMeter (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) : Charged (List Branch) :=
 let h:=hardBranchMeter S a b;let s:=bBranchMeter S b qb;let l:=targetBranchMeter T (qa::qs)
 ⟨[h.value,s.value,l.value],h.work+s.work+l.work+4⟩
@[simp] theorem type_i_value (T S : Tree) (a b : Nat) (qa qb q r : RMAF.Vertex) :
 (typeIMeter T S a b qa qb q r).value=typeIBranches T S a b qa qb q r:=by simp [typeIMeter,typeIBranches]
@[simp] theorem type_ii_value (T S : Tree) (a b : Nat) (qa qb : RMAF.Vertex) (qs : List RMAF.Vertex) :
 (typeIIMeter T S a b qa qb qs).value=typeIIBranches T S a b qa qb qs:=by simp [typeIIMeter,typeIIBranches]

def rawPlanMeter (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) : Charged (List Branch) :=
 let es:=cSideMeter T b c
 match es.value with
 | q::r::_=>let p:=typeIMeter T S a b qa qb q r;⟨p.value,es.work+p.work+3⟩
 | _=>let bs:=withoutAMeter T a b c
      match bs.value with
      | []=>let l:=lcaMeter ub uc;let p:=typeIIMeter T S a b qa qb [l.value];⟨p.value,es.work+bs.work+l.work+p.work+5⟩
      | qs=>let p:=typeIIMeter T S a b qa qb qs;⟨p.value,es.work+bs.work+p.work+3⟩

@[simp] theorem raw_plan_value (T S : Tree) (a b c : Nat) (qa qb ub uc : RMAF.Vertex) :
 (rawPlanMeter T S a b c qa qb ub uc).value=rawPlan T S a b c qa qb ub uc := by
 simp only [rawPlanMeter,c_side_meter_value,without_a_value,lca_value,type_i_value,type_ii_value,rawPlan]
 split <;> first | rfl | split <;> rfl

def literalPlanMeter {T S : Tree} (D : LiteralGeometry T S) : Charged (List Branch) :=
 let p:=rawPlanMeter T S D.a D.b D.c D.qa (bArc D.w D.sb) D.ub D.uc
 ⟨p.value,p.work+D.w.length+2⟩
@[simp] theorem literal_plan_value {T S : Tree} (D : LiteralGeometry T S) :
 (literalPlanMeter D).value=literalPlan D:=by simp [literalPlanMeter,literalPlan]
end Universal233.Rule5ExecutionSource
