import PaidControls
namespace Universal233.Hard2PaidLocal.Controls
open RMAF CoreProgram BothBad SourceCoverage
set_option maxRecDepth 10000
example : (runOutputs noOrd source3 source3 2 tripleOutputs).calls.all (fun call=>call.budget==1)=true := by decide
example : traceMass 2 1 (runOutputs noOrd source source 1 [cut,cut]).calls=0 := by
 rw [duplicates_paid.1]; decide
example : rawQMass 2 [cut,cut]=0 := by
 rw [duplicates_paid.2]; decide
example : (checked source source 1 (some [[999]])).isSome=true := by decide
example : restrictionAgrees source5 target5 [0,1,2]=true := by decide
end Universal233.Hard2PaidLocal.Controls
