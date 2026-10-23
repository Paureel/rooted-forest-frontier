import RILifetime
open OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryBits
private def twoInput : InputTree := .node (.leaf [true]) (.leaf [false,true])
private def palette : List (List (List Bool)) := [[[true],[false,true]]]
private def fourInput : InputTree := .node (.node (.leaf []) (.leaf [true])) (.node (.leaf [false,true]) (.leaf [true,true]))
example : (copyInput (.leaf [true,false])).work = 13 := by decide +kernel
example : (closeInput (.leaf [true,false])).work = 13 := by decide +kernel
example : (initializeBits 3 (.node (.leaf [true]) (.leaf [true,false])) [] []).value = none := by decide +kernel
example : ((initializeBits 3 twoInput palette [true,true,true]).value.map (fun p=>decode p.1)) = some 1 := by decide +kernel
example : (normalizeBits (.node [] (.leaf ⟨[false],[[true]],[true]⟩) (.leaf ⟨[true],[[false,true]],[true,false]⟩))).value = .leaf ⟨[],[[true],[false,true]],[true]⟩ := by decide +kernel
example : ((initializeBits 2 fourInput [] [true,true]).value.map (fun p=>decode p.1)) = some 0 := by decide +kernel
example : (lengthOwned 2 [0,1,2,3]).value.length = 2 := by decide +kernel
example : decode (lengthOwned 2 [0,1,2,3]).value = 0 := by decide +kernel
example : (initializeBits 3 (.node (.leaf [true]) (.leaf [true,false])) [[[true]]] []).work > (initializeBits 3 (.node (.leaf [true]) (.leaf [true,false])) [] []).work := by decide +kernel
example : (assemble [] (.leaf ⟨[false],[[true]],[true]⟩) (.leaf ⟨[true],[[false,true]],[true,false]⟩)).work > (closeTree (.leaf ⟨[false],[[true]],[true]⟩)).work+(closeTree (.leaf ⟨[true],[[false,true]],[true,false]⟩)).work := by decide +kernel
