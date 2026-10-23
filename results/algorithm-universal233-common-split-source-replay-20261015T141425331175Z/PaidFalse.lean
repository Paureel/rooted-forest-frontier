import PaidControls
open OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Caller.PaidControls
example : (paidJobs d 2).map Job.budget=[2,2] := by decide
example : replyCost (runPaid d 1 FY Controls.FN cb)=some 2 := by decide
