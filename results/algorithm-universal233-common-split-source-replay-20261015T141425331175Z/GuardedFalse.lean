import GuardedControls
open OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Caller.PaidControls
example : runGuarded d 0 cb=none := by decide
example : (guardedJobs d 2).map Job.budget=[0,0] := by decide
