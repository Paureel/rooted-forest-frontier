import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def s : Tree := .node (.leaf 0) (.leaf 1)
private def d : Universal233.Rule5FinalClassification.BadSelection := ⟨[],[],0⟩
example : (sourceForestMeter s [[0],[],[0],[8]]).value=[.leaf 0,.leaf 0] := by decide +kernel
example : (makeChildMeter s [[0],[],[0],[8]] 7).value.paid=7 := by decide +kernel
example : (excludeOneMeter 0 [0,1,0,2]).value=[1,2] := by decide +kernel
example : (excludeOneMeter 0 [0,1,0,2]).work=13 := by decide +kernel
example : (excludeTwoMeter 0 1 [0,1,0,2]).value=[2] := by decide +kernel
example : (excludeTwoMeter 0 1 [0,1,0,2]).work=17 := by decide +kernel
example : (siblingEndpointMeter s [false]).value=some 1 := by decide +kernel
example : (siblingEndpointMeter s [false]).work=12 := by decide +kernel
example : (siblingEndpointMeter s []).work=2 := by decide +kernel
example : ForestArm (.prefix .remaining) := by unfold ForestArm; decide +kernel
example : ¬ForestArm (.remaining d (.one [])) := by unfold ForestArm; decide +kernel
example : ¬ForestArm (.remaining d (.second [] [])) := by unfold ForestArm; decide +kernel
example : (selectedChildrenMeter s 0 1 (.remaining d (.one []))).value.length=0 := by decide +kernel
