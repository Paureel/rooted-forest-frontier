import OWBudgets
import RWInterface
import ClosedSourceTree
namespace OrdinaryDispatch.GlobalSourceAssembly
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.OptimizerLocalWork OrdinaryDispatch.BudgetOptimization

/-- Exactly one literal final recovery, now using the completed recovery SOURCE
meter. Query callback work w is still explicit and is not a solve-cost claim. -/
def sourceFinishMeter (S : Tree) (r : Scan) : Charged Execution :=
 match r.selected with
 | none=>⟨⟨r,none,[]⟩,8⟩
 | some (_,F)=>
  let a:=RecoveryLocalWork.meterRecover S F
  ⟨⟨r,a.value,[(F,a.value)]⟩,a.work+12⟩

theorem sourceFinishMeter_value (S : Tree) (r : Scan) : (sourceFinishMeter S r).value=finish S r := by
 cases h:r.selected with
 | none=>simp [sourceFinishMeter,finish,h]
 | some p=>obtain ⟨q,F⟩:=p;simp [sourceFinishMeter,finish,h,RecoveryLocalWork.meterRecover_value]

def recoverySourceDebit (S : Tree) (r : Execution) : Nat :=
 (r.recoveries.map (fun call=>(RecoveryLocalWork.meterRecover S call.1).work)).sum

theorem sourceFinishMeter_bound (S : Tree) (r : Scan) :
 (sourceFinishMeter S r).work≤12+recoverySourceDebit S (finish S r) := by
 cases h:r.selected with
 | none=>simp [sourceFinishMeter,finish,recoverySourceDebit,h]
 | some p=>
  obtain ⟨q,F⟩:=p
  simp only [sourceFinishMeter,finish,recoverySourceDebit,h,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

/-- Actual finite scan with a source-metered final recovery. The interpretation
of w must be supplied separately; the closed subtotal instantiation below is
explicitly partial while hard2/Rule5 source handlers remain absent. -/
def sourceOptimizeMeter (w : Nat→Nat) (T S : Tree) : Charged Execution :=
 let p:=meterPreflight T S
 if p.value.1 then
  let s:=meterScan (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 p.value.2
  let f:=sourceFinishMeter S s.value
  ⟨f.value,p.work+s.work+f.work+8⟩
 else ⟨⟨⟨none,[]⟩,none,[]⟩,p.work+8⟩

theorem sourceOptimizeMeter_value (w : Nat→Nat) (T S : Tree) :
 (sourceOptimizeMeter w T S).value=optimize T S := by
 simp only [sourceOptimizeMeter,meterPreflight_value,sourceFinishMeter_value,meterScan_value,optimize]
 split <;> rfl

def sourceTotalCharge (w : Nat→Nat) (preflight perTrial finalRecord : Nat) (S : Tree) (r : Execution) : Nat :=
 trialWork w r.search.trials+wrapperCharge preflight perTrial finalRecord r+recoverySourceDebit S r

theorem optimizer_fee_nat (pw sw fw pre tw admin calls rec : Nat)
 (p : pw≤pre) (s : sw=tw+admin) (a : admin≤12*calls+2) (f : fw≤12+rec) :
 pw+sw+fw+8≤tw+(pre+12*calls+32)+rec := by omega

theorem optimizer_refusal_nat (pw pre : Nat) (p : pw≤pre) : pw+8≤0+(pre+12*0+32)+0 := by omega

/-- Preflight, every retained failed/successful trial, final records and the
one selected source recovery are derived at their literal source sites. -/
theorem sourceOptimize_actual_fees (w : Nat→Nat) (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) :
 (sourceOptimizeMeter w T S).work≤sourceTotalCharge w (preflightFee N) 12 32 S (optimize T S) := by
 have p:=meterPreflight_bound T S N tn sn
 by_cases hp:DepthOne.proper T S=true
 · let sc:=meterScan (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 (leaves T).length
   have sv : sc.value=scan (fun b=>FastOrdinary.solve b T S) 0 (leaves T).length:=by
    simp only [sc,meterScan_value]
   have sw:=meterScan_accounting (fun b=>⟨FastOrdinary.solve b T S,w b⟩) 0 (leaves T).length
   change sc.work=trialWork w sc.value.trials+sc.administration at sw
   have sa:sc.administration≤12*sc.value.trials.length+2:=(meterScan_administration _ _ _).1
   have f:=sourceFinishMeter_bound S sc.value
   have result : optimize T S=finish S sc.value:=by simp only [optimize,hp,ite_true,sv]
   have bound:=optimizer_fee_nat _ _ _ _ _ _ _ _ p sw sa f
   simp only [sourceOptimizeMeter,meterPreflight_value,hp,ite_true]
   rw [result]
   simpa only [sourceTotalCharge,wrapperCharge,finish_search,sc] using bound
 · have hf:DepthOne.proper T S=false:=Bool.eq_false_iff.2 hp
   have bound:=optimizer_refusal_nat _ _ p
   simpa only [sourceOptimizeMeter,meterPreflight_value,hf,Bool.false_eq_true,ite_false,optimize,sourceTotalCharge,
    trialWork,wrapperCharge,recoverySourceDebit,List.map_nil,List.sum_nil,List.length_nil] using bound
end OrdinaryDispatch.GlobalSourceAssembly
