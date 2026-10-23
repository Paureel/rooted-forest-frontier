import PaidArcWork
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open CherryBranching Rule5Case322 Rule5PendantLocalWork

def vertexNodupMeter : List RMAF.Vertex→Charged Bool
 | []=>⟨true,1⟩
 | q::qs=>let c:=containsAddressMeter q qs;let r:=vertexNodupMeter qs
           ⟨!c.value&&r.value,c.work+r.work+3⟩
@[simp] theorem vertex_nodup_value (qs : List RMAF.Vertex) :
 (vertexNodupMeter qs).value=decide qs.Nodup := by
 apply Bool.eq_iff_iff.2
 induction qs <;> simp_all [vertexNodupMeter,List.nodup_cons,contains_address_value]

def natListEqMeter : List Nat→List Nat→Charged Bool
 | [],[]=>⟨true,1⟩ | [],_::_=>⟨false,1⟩ | _::_,[]=>⟨false,1⟩
 | x::xs,y::ys=>let r:=natListEqMeter xs ys;⟨(x==y)&&r.value,r.work+3⟩
@[simp] theorem nat_list_eq_value (xs ys : List Nat) : (natListEqMeter xs ys).value=(xs==ys) := by
 induction xs generalizing ys <;> cases ys <;> simp_all [natListEqMeter,List.cons_beq_cons]
theorem nat_list_eq_work (xs ys : List Nat) : (natListEqMeter xs ys).work≤3*(xs.length+ys.length+1) := by
 induction xs generalizing ys <;> cases ys <;> simp_all only [natListEqMeter,List.length_nil,List.length_cons] <;> omega

def forestEqMeter : List (List Nat)→List (List Nat)→Charged Bool
 | [],[]=>⟨true,1⟩ | [],_::_=>⟨false,1⟩ | _::_,[]=>⟨false,1⟩
 | B::P,C::Q=>let a:=natListEqMeter B C;let r:=forestEqMeter P Q;⟨a.value&&r.value,a.work+r.work+3⟩
@[simp] theorem forest_eq_value (P Q : List (List Nat)) : (forestEqMeter P Q).value=(P==Q) := by
 induction P generalizing Q <;> cases Q <;> simp_all [forestEqMeter,List.cons_beq_cons]
theorem forest_eq_work (P Q : List (List Nat)) :
 (forestEqMeter P Q).work≤6*(P.flatten.length+Q.flatten.length+P.length+Q.length+1) := by
 induction P generalizing Q with
 | nil=>cases Q <;> simp only [forestEqMeter,List.flatten_nil,List.length_nil,List.length_cons] <;> omega
 | cons B P ih=>cases Q with
  | nil=>simp only [forestEqMeter,List.length_nil,List.length_cons];omega
  | cons C Q=>
   have a:=nat_list_eq_work B C;have r:=ih Q
   simp only [forestEqMeter,List.flatten_cons,List.length_append,List.length_cons];omega

/-- Literal currentGuard components. Full-suffix meters overcharge Boolean
short circuits, while repeated subtree and arc-partition work stays present. -/
def currentGuardMeter (T S : Tree) (c : Branch) : Charged Bool :=
 let n:=vertexNodupMeter c.originalCuts
 let a:=meterAll (fun q=>let s:=meterSubtree (current T S c) q;⟨!q.isEmpty&&s.value.isSome,s.work+3⟩) c.originalCuts
 let l:=meterLeaves (current T S c)
 let p:=meterPartition l.value c.partition
 let e:=meterPairwise (current T S c) c.partition
 let r:=arcPartitionMeter (current T S c) c.originalCuts
 let eq:=forestEqMeter c.partition r.value
 ⟨n.value&&a.value&&p.value&&e.value&&(c.partition.length==c.originalCuts.length+1)&&eq.value,
  n.work+a.work+l.work+p.work+e.work+r.work+eq.work+c.partition.length+2*c.originalCuts.length+18⟩

@[simp] theorem current_guard_value (T S : Tree) (c : Branch) :
 (currentGuardMeter T S c).value=currentGuard T S c := by
 simp only [currentGuardMeter,vertex_nodup_value,meterAll_value,meterSubtree_value,meterLeaves_value,
  meterPartition_value,meterPairwise_value,arc_partition_value,forest_eq_value,currentGuard,paid]

def guardedPlanMeter {T S : Tree} (D : Case322PaidGuard.LiteralGeometry T S)
 (plan : Charged (List Branch)) : Charged (List Branch) :=
 let f:=meterFilter (currentGuardMeter T S) plan.value;⟨f.value,plan.work+f.work+2⟩

theorem guarded_plan_value {T S : Tree} (D : Case322PaidGuard.LiteralGeometry T S)
 (plan : Charged (List Branch)) (val : plan.value=Case322PaidGuard.literalPlan D) :
 (guardedPlanMeter D plan).value=Case322PaidGuard.guardedPlan D := by
 simp only [guardedPlanMeter,meterFilter_value,current_guard_value,val,Case322PaidGuard.guardedPlan]
end Universal233.Rule5ExecutionSource
