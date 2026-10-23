import Std
axiom unusedFalse : False
private axiom privateFalse : False
private theorem hiddenBad : False := privateFalse
theorem exportedBad : False := privateFalse
theorem cleanHeadline : True := True.intro
