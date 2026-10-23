import RILifetime
open OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryBits
private def twoInput : InputTree := .node (.leaf [true]) (.leaf [false,true])
private def palette : List (List (List Bool)) := [[[true],[false,true]]]
private def fourInput : InputTree := .node (.node (.leaf []) (.leaf [true])) (.node (.leaf [false,true]) (.leaf [true,true]))
example : ((initializeBits 2 fourInput [] [true,true]).value.map (fun p=>decode p.1)) = some 3 := by decide +kernel
