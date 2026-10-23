import Controls
open RMAF Universal233.CherryBranching Universal233.CherryBranching.Pre
example : (pendantChild s3 0 1).paid = 2 := by decide
example : (pendantChild s3up 0 1).partition.flatten.contains 6 = true := by decide
example : pairwiseEmbeddings s3 [[0,1],[2,3,4]] = true := by decide
example : (select t1 s1).map Prod.fst = some .high := by decide
example : remaining 2 (pendantChild s3 0 1) = some 0 := by decide
