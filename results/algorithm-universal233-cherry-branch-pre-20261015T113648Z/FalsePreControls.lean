import PreControls
open RMAF Universal233.HardParent Universal233.CherryBranching.Pre
example : (pendantOriginal s3 0 1).length = 2 := by decide
example : (post s3up 0 1).flatten.contains 6 = true := by decide
example : pairwiseEmbeddings source4 [[0,1],[2,3]] = true := by decide
example : (post s3up 0 1).flatten.contains 5 = false := by decide
example : (post s1 0 1).any (fun B => [0,2].all B.contains) = true := by decide
