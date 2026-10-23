import ClusterFreeWitness
open RMAF Universal233.ScaffoldWitness Universal233.ClusterFreeWitness
example : noProperCommon originalT originalS = true := by decide
example : noProperCommon clusterFreeT originalS = false := by decide
example : everyBadParentRejectsOneCut = false := by decide
