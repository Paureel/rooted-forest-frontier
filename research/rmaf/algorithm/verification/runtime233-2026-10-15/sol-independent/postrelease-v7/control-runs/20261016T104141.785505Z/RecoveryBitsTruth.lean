import RSCopyBounds
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryScalar
example : decode (clipBudget 3 [true,true,true] [1,2,3]).value = 2 := by decide +kernel
example : (containsBits [true,false,false] [[true]]).value = true := by decide +kernel
example : decode (colorBits [[[true],[false,true]],[[true,true]]] [false,true]).value = 1 := by decide +kernel
example : (copyGroup ⟨[false,true],[[true,false],[false,true]],[true]⟩).work = 54 := by decide +kernel
example : (copyTree (.leaf ⟨[false,true],[[true,false],[false,true]],[true]⟩)).work = 58 := by decide +kernel
example : (copyOutput ⟨[[[true]],[]],[[false]]⟩).work = 42 := by decide +kernel
example : decode (counterAdd 3 [true,true,true] [true]).value = 0 := by decide +kernel
example : scalarWidth 3 2 5 = 21 := by decide +kernel
