import OWOptimize
namespace OrdinaryDispatch.OptimizerLocalWork.Controls
open RMAF Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.BudgetOptimization
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

def synthetic (q : Nat) : Charged (Option CommonForest):=⟨if q=1 then some [[0]] else none,q+1⟩
def failed (_ : Nat) : Charged (Option CommonForest):=⟨none,1⟩
def sscan:=meterScan synthetic 0 3
def fscan:=meterScan failed 0 3

theorem scan_known : sscan.value.trials=[(0,none),(1,some [[0]])] ∧
 sscan.administration=24 ∧ sscan.work=27 ∧
 trialWork (fun q=>(synthetic q).work) sscan.value.trials=3 := by decide

theorem failure_known : fscan.value.trials=[(0,none),(1,none),(2,none)] ∧
 fscan.administration=38 ∧ fscan.work=41 := by decide

theorem null_known : (meterScan synthetic 0 0).value.trials=[] ∧
 (meterScan synthetic 0 0).value.selected=none ∧
 (meterScan synthetic 0 0).work=2 := by decide

theorem length_known : (meterLength ([0,1,2]:List Nat)).work=14 ∧
 (meterLength ([0,1,2]:List Nat)).value=3 := by decide

theorem guards_known :
 [(meterInputCheck (.leaf 7) [[7]]).value,(meterInputCheck (.leaf 7) []).value,
  (meterInputCheck (.leaf 7) [[7],[7]]).value,
  (meterInputCheck (.leaf 7) (List.replicate 40 [7])).value]=[true,false,false,false] := by decide

def triT : Tree:=.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def triS : Tree:=.node (.leaf 0) (.node (.leaf 1) (.leaf 2))
def malformed : Tree:=.node (.leaf 7) (.leaf 7)
def summary (r : Execution):=
 (r.search.selected.map Prod.fst,r.search.trials.map (fun t=>(t.1,t.2.isSome)),r.recoveries.length,
 r.output.map (fun o=>(o.sourceCuts.length,o.partition.length)))
def runtimeChecks : List (String×Bool):=
 [("singleton",summary (meterOptimize (fun _=>0) (.leaf 7) (.leaf 7)).value==(some 0,[(0,true)],1,some (0,1))),
  ("identical",summary (meterOptimize (fun _=>0) triT triT).value==(some 0,[(0,true)],1,some (0,1))),
  ("triple",summary (meterOptimize (fun _=>0) triT triS).value==(some 1,[(0,false),(1,true)],1,some (1,2))),
  ("malformed",summary (meterOptimize (fun _=>0) malformed malformed).value==(none,[],0,none)),
  ("unequal",summary (meterOptimize (fun _=>0) (.leaf 7) (.leaf 8)).value==(none,[],0,none)),
  ("malformed_bill",(meterOptimize (fun _=>0) malformed malformed).work>0),
  ("recovery_singleton",(meterRecovery (.leaf 7) [[7]]).value.map (fun o=>(o.sourceCuts.length,o.partition.length))==some (0,1)),
  ("recovery_refused",(meterRecovery (.leaf 7) []).value.isNone),
  ("raw_guard_work",(meterInputCheck (.leaf 7) (List.replicate 40 [7])).work>(meterInputCheck (.leaf 7) [[7]]).work),
  ("block_color",FinalCutRecovery.blockColor [[],[7]] 7==7)]
#eval ("SCAN_KNOWN",sscan.value.trials.map (fun t=>(t.1,t.2.isSome)),sscan.administration,sscan.work)
#eval ("FAIL_KNOWN",fscan.value.trials.map (fun t=>(t.1,t.2.isSome)),fscan.administration,fscan.work)
#eval runtimeChecks
#eval ("PASS_OPTIMIZER_LOCAL_CONTROLS",runtimeChecks.length,runtimeChecks.all Prod.snd)
#eval ("RAW_GUARD_WORK",(meterInputCheck (.leaf 7) [[7]]).work,(meterInputCheck (.leaf 7) (List.replicate 40 [7])).work)
end OrdinaryDispatch.OptimizerLocalWork.Controls
