import RSCopyBounds
open OrdinaryDispatch.RecoveryBits
example : decode (counterAdd 3 [true,true,true] [true]).value = 8 := by decide +kernel
