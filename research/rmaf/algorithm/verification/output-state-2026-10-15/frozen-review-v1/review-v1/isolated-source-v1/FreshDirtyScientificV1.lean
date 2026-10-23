import ResidualConsumer
namespace FreshTargetDirty
axiom unusedFalse : False
private axiom hiddenFalse : False
private theorem hiddenBad : False := hiddenFalse
theorem cleanHeadline : True := True.intro
end FreshTargetDirty
