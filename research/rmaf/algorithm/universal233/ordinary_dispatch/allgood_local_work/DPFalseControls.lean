import DPControls
open AllGoodDP AllGoodDP.LocalWork AllGoodDP.LocalWork.Controls
example : (meterChanges P).work≤1 := by cbv
example : (meterTable [0,1,2,3] (fun x=>⟨x,4⟩) T).work≤1 := by cbv
example : (meterRun (some T) bad).value.isSome=true := by cbv
example : (meterRun (some T) ss).work≤1 := by cbv
