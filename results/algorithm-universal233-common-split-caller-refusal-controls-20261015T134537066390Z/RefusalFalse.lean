import GuardRefusalControls
open OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Caller.GuardRefusalControls OrdinaryCommonSplit.Caller.PaidControls
example : runGuarded equalPair 2 cb=some none := by decide
