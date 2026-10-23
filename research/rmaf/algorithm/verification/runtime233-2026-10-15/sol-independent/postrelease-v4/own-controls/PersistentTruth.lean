import PersistentEntry
open GenericForest.BinaryProvider
example : (zeroRegister [(),()]).work=9 := by decide +kernel
example : (widenCapacity [] [false,false,false]).value.length=3 := by decide +kernel
example : (widenCapacity [] [false,false,false]).work=13 := by decide +kernel
example : (spineCounter [10,20,30]).value=[true,true] := by decide +kernel
example : (countLabel [(),()] [true] [[true],[true,false],[]]).value=[false,true] := by decide +kernel
example : (partitionFromInput [[true]] [[[true,false]]]).value=true := by decide +kernel
example : (partitionFromInput [[true]] [[[true],[true,false]]]).value=false := by decide +kernel
example : (checkerFromInput none [] [] []).value.isSome=true := by decide +kernel
example : (checkerFromInput (some (.leaf [true])) [.leaf [true,false]] [] [[[true]]]).value.isSome=true := by decide +kernel
example : (checkerFromInput (some (.node (.leaf [true]) (.leaf [true,false]))) [.node (.leaf [true]) (.leaf [true,false])] [] [[[true]]]).value.isNone=true := by decide +kernel
