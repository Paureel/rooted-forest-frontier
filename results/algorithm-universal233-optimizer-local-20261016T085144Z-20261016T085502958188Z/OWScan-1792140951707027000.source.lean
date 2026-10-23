import BOConditional
import ERInterface
namespace OrdinaryDispatch.OptimizerLocalWork
open RMAF Universal233 WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.BudgetOptimization

/-- List-length traversal has a fee per cell, including the terminal branch. -/
def meterLength {α : Type} : List α→Charged Nat
 | []=>⟨0,2⟩
 | _::xs=>let r:=meterLength xs;⟨r.value+1,r.work+4⟩
@[simp] theorem meterLength_value {α : Type} (xs : List α) : (meterLength xs).value=xs.length := by
 induction xs <;> simp_all [meterLength]
theorem meterLength_work {α : Type} (xs : List α) : (meterLength xs).work=4*xs.length+2 := by
 induction xs <;> simp_all [meterLength,Nat.mul_add]

def meterPreflight (T S : Tree) : Charged (Bool×Nat) :=
 let p:=meterOrdinaryProper T S;let l:=meterLeaves T;let n:=meterLength l.value
 ⟨(p.value,n.value),p.work+l.work+n.work+8⟩
@[simp] theorem meterPreflight_value (T S : Tree) :
 (meterPreflight T S).value=(DepthOne.proper T S,(leaves T).length) := by simp [meterPreflight]

def preflightFee (N : Nat) : Nat:=256*(N+1)^2

theorem meterPreflight_bound (T S : Tree) (N : Nat)
 (tn : treeNodes T≤N) (sn : treeNodes S≤N) : (meterPreflight T S).work≤preflightFee N := by
 have p:=meterOrdinaryProper_bound T S N tn sn
 have l:=meterLeaves_cap T N tn
 have ln:=Nat.le_trans (leaves_nodes T) tn
 have len:=meterLength_work (leaves T)
 have p1 : N+1≤(N+1)^2:=by simpa using pow_mono N 1 2 (by decide)
 have pos : 1≤(N+1)^2:=Nat.one_le_pow _ _ (by omega)
 simp only [meterPreflight,meterLeaves_value,preflightFee];omega

structure ScanMeasured where
 value : Scan
 work : Nat
 administration : Nat

/-- Callback value/work is explicit. A retained forest is a reference; its cells
are not traversed or encoded by scan. Nat increment remains a scalar slot. -/
def meterScan (query : Nat→Charged (Option CommonForest)) (start : Nat) : Nat→ScanMeasured
 | 0=>⟨⟨none,[]⟩,2,2⟩
 | fuel+1=>let a:=query start
   match a.value with
   | some F=>⟨⟨some (start,F),[(start,a.value)]⟩,a.work+12,12⟩
   | none=>let r:=meterScan query (start+1) fuel
     ⟨⟨r.value.selected,(start,a.value)::r.value.trials⟩,a.work+r.work+12,r.administration+12⟩
@[simp] theorem meterScan_value (query : Nat→Charged (Option CommonForest)) (start fuel : Nat) :
 (meterScan query start fuel).value=scan (fun q=>(query q).value) start fuel := by
 induction fuel generalizing start with
 | zero=>rfl
 | succ fuel ih=>cases h:(query start).value <;> simp [meterScan,scan,h,ih]

theorem meterScan_accounting (query : Nat→Charged (Option CommonForest)) (start fuel : Nat) :
 (meterScan query start fuel).work=
 trialWork (fun q=>(query q).work) (meterScan query start fuel).value.trials+
 (meterScan query start fuel).administration := by
 induction fuel generalizing start with
 | zero=>rfl
 | succ fuel ih=>
  have a:=ih (start+1)
  simp only [trialWork] at a
  cases h:(query start).value <;> simp only [meterScan,h]
   <;> simp only [ScanMeasured.work,ScanMeasured.value,ScanMeasured.administration,trialWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
   <;> omega

theorem meterScan_administration (query : Nat→Charged (Option CommonForest)) (start fuel : Nat) :
 (meterScan query start fuel).administration≤12*(meterScan query start fuel).value.trials.length+2 ∧
 (meterScan query start fuel).value.trials.length≤fuel := by
 induction fuel generalizing start with
 | zero=>simp [meterScan]
 | succ fuel ih=>
  have htail:=ih (start+1)
  cases h:(query start).value <;> simp only [meterScan,h]
   <;> simp only [ScanMeasured.administration,ScanMeasured.value,List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one]
   <;> omega

theorem actual_scanned_budget_cap (T S : Tree) (q : Nat) (F : CommonForest)
 (selected : (scan (fun b=>FastOrdinary.solve b T S) 0 (leaves T).length).selected=some (q,F)) :
 q<(leaves T).length := by
 obtain ⟨sk,eq,lt,rest⟩:=scan_success _ _ _ _ _ selected
 omega
end OrdinaryDispatch.OptimizerLocalWork
