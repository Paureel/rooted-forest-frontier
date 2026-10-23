import Polynomial
namespace AllGoodDP.LocalWork.Controls
open RMAF ForestState Universal233.WholeSourceWork

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def ss : List Tree := [.leaf 0,.leaf 1,.leaf 2,.leaf 3]
def bad : List Tree := [.leaf 0,.leaf 0,.leaf 2,.leaf 3]
def P : Paint := .node 0 (.node 1 (.leaf 0 0) (.leaf 1 1)) (.node 2 (.leaf 2 2) (.leaf 3 3))
def huge : Tree := .node (.leaf 1000000000000000000000000000000) (.leaf 9999999999999999999999999999999)
theorem actual_proper : proper (some T) ss=true := by decide
theorem actual_scan : (meterChanges P).work=64 := by cbv
theorem actual_scan_value : (meterChanges P).value=4 := by cbv
theorem polynomial : (meterRun (some T) ss).work≤1048576*5^4 := actual_run_polynomial T ss actual_proper
theorem malformed : (meterRun (some T) bad).value=none := by rw [meterRun_value];decide

#eval decide ((meterRun (some T) ss).value=run (some T) ss)
#eval decide ((meterRun (some T) [T]).value=run (some T) [T])
#eval decide ((meterRun (some T) [.node (.leaf 0) (.leaf 1),.node (.leaf 2) (.leaf 3)]).value=run (some T) [.node (.leaf 0) (.leaf 1),.node (.leaf 2) (.leaf 3)])
#eval decide ((meterRun (some T) bad).value=none)
#eval decide ((meterRun none []).value=run none [])
#eval decide ((meterRun (some huge) [huge]).value=run (some huge) [huge])
#eval decide ((meterTable [] (fun x=>⟨x,4⟩) T).value=table [] id T)
#eval decide ((meterTable [1,1,2] (fun x=>⟨x,4⟩) T).value=table [1,1,2] id T)
#eval decide ((meterTable [0,1,2,3] (fun x=>⟨x,4⟩) T).work>visits 4 T)
end AllGoodDP.LocalWork.Controls
