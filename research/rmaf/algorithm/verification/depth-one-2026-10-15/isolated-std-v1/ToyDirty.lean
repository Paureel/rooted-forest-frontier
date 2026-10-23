import Std
namespace DepthToy
axiom unusedFalse : False
private axiom secretFalse : False
private theorem hiddenBad : False := secretFalse
axiom usedFalse : False
theorem exportedBad : False := usedFalse
theorem cleanHeadline : True := True.intro
end DepthToy
