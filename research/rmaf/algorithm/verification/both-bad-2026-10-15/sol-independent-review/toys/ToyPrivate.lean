import ToyGood
namespace ToyPrivate
private axiom privateCustom : False
private theorem producer : False := privateCustom
theorem innocent : True := True.intro
end ToyPrivate
