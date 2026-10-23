import FinalControls
open RMAF Universal233.Rule5FinalClassification Universal233.Rule5FinalClassification.Controls
open Universal233.Rule5Local Universal233.Rule5Local.Pre Universal233.CherryBranching
open Universal233.CoreGraph
example : selectBad sixT sixS 0 1=some ⟨[false,true],[false,false,true],2⟩ := by decide
example : selectBoundary sixT [14,15,16] 2=some (.first [false,true] [false,false,false,true]) := by decide
example : selectBoundary rootT [3,6,7,8,5,4] 2=some (.one []) := by decide
example : admitted noRule4T noRule4S 0 1=true := by decide
example : (incident overlapT [14,15,16]).length≤2 := by decide
example : subtree thirdT [false]=some (.leaf 0) := by decide
example : restrictionAgrees firstT firstS (coreLabels firstS 0 1)=false := by decide
example : selectFinal firstT firstS 0 1=none := by decide
