import PendantWorkControls
open Universal233.Rule5PendantLocalWork RMAF
example : (verticesMeter smallT).value.length≤3 := by decide
example : (cutsMeter smallT 0 1).work=0 := by decide
example : (partitionMeter smallT 0 1).work≤1 := by decide
example : (admittedMeter fee sixT sixS 0 1).calls.length=4 := by decide
