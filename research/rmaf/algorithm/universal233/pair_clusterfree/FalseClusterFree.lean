import ClusterFreeWitness
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
open RMAF Universal233.ScaffoldWitness Universal233.ClusterFreeWitness
example : noProperCommon originalT originalS = true := by decide
example : noProperCommon clusterFreeT originalS = false := by decide
example : everyBadParentRejectsOneCut = false := by decide
