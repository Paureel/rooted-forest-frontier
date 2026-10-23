import RILifetime
open OrdinaryDispatch.RecoveryInitialBits OrdinaryDispatch.RecoveryBits
private def twoInput : InputTree := .node (.leaf [true]) (.leaf [false,true])
private def palette : List (List (List Bool)) := [[[true],[false,true]]]
private def fourInput : InputTree := .node (.node (.leaf []) (.leaf [true])) (.node (.leaf [false,true]) (.leaf [true,true]))
example : (normalizeBits (.node [] (.leaf ⟨[false],[[true]],[true]⟩) (.leaf ⟨[true],[[false,true]],[true,false]⟩))).value = .node [] (.leaf ⟨[false],[[true]],[true]⟩) (.leaf ⟨[true],[[false,true]],[true,false]⟩) := by decide +kernel
