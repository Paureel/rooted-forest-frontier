import ExtractionRootControls
open RMAF Universal233.Rule5Case322 Universal233.Case322Extraction Universal233.Case322Extraction.Controls
example : currentGuard falseBindingT falseBindingS (bBranch falseBindingS 1 [false,true]) = true := by decide
example : (rawPlan core0nT core0nS 0 1 2 [false,false,false,true,false,false] [false,true] [false,false,false,true,false,true] [false,true]).map paid = [2,1,2] := by decide
example : (rawPlan rootT rootS 0 1 2 [false,false] [true] [false,true] [true,false]).all (currentGuard rootT rootS) = true := by decide
